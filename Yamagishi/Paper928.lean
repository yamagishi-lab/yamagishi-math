/-
論文928『ジョーンズ多項式は、低い次数の 1 の冪根では右と左を見分けられない』の格上げ（芯だけ）。

日本語の一文：結び目のジョーンズ多項式について、V − 1 が (1 − t)(1 − t³) で割り切れることと V(i) が実数で
あることを入力に置くと、鏡像との差 t^M(V(t) − V(1/t)) はいつも (t − 1)³(t + 1)(t² + 1)(t² + t + 1) で
割り切れ、次数が −4 から 4 に収まる結び目では、鏡像と値が一致する t は ±1・±i・ω・ω² の六つだけである。
English: Core only: write a knot's Jones polynomial as V(t) = 1 + (t − 1)(t³ − 1)P(t)/t^M with
deg P ≤ N = 2M − 4 (Jones: (1 − t)(1 − t³) divides V − 1) and assume V(i) = V(−i) (V(i) is real and
the coefficients are real); then D = t^M(V(t) − V(1/t)) is a polynomial divisible by
W = (t − 1)³(t + 1)(t² + 1)(t² + t + 1); if M ≤ 4 and V(t) ≢ V(1/t), V(t) = V(1/t) holds exactly
at the six points ±1, ±i, ω, ω²; if M ≤ 3 then V(t) = V(1/t) for every t ≠ 0. The trefoil and 6₁
are checked.

原稿（928_yamagishi_the_jones_polynomial_cannot_tell_left_from_right_at_low_roots_of_unity/…_jp.tex）は、
3₁・4₁・5₁・5₂ とホップ絡み目の多項式で、t = 1・ω・−1・i では鏡像と同じ値、t = 2 と e^(iπ/5) では違う値に
なることを数値で示しただけで、「それ以外の t では必ず違う」の向きと割り切れの形は書いていない。

ここで証明した言明（P は複素係数の多項式、natDegree P ≤ N、N + 4 = 2M）：
  (1) `eval_D`：D = (X − 1)(X³ − 1)(P − reflect_N P) は、t ≠ 0 で D(t) = t^M(V(t) − V(1/t)) をみたす。
  (2) `W_dvd_D`：V(i) = V(−i) なら W ∣ D（t = 1 は三重、−1・±i・ω・ω² は一重の根）。
      `Vi_eq_of_real`：係数が実数で V(i) が実数なら V(i) = V(−i)（V(−i) は V(i) の複素共役）。
  (3) `eval_W_eq_zero_iff`：W(t) = 0 ⇔ t は 1・−1・i・−i・ω・ω² のどれか（ω = −1/2 + (√3/2)i）。
  (4) `six_points`：M ≤ 4 で D ≠ 0 なら、t ≠ 0 について V(t) = V(1/t) ⇔ t がその六点のどれか。
      `symmetric_of_small`：M ≤ 3 なら、すべての t ≠ 0 で V(t) = V(1/t)（鏡像と区別できない）。
  (5) `trefoil_V`・`trefoil_D`：右手の三つ葉 V = t + t³ − t⁴（P = −X⁴）で D = −W。
      `knot61_V`・`knot61_D`：6₁ の V = t⁻⁴ − t⁻³ + t⁻² − 2t⁻¹ + 2 − t + t²（P = X² + 1）でも D = −W。
      `trefoil_six_points`：三つ葉では V(t) = V(1/t) ⇔ t が六点のどれか。
足した仮定（ここが「芯だけ」の理由）：Mathlib に結び目とジョーンズ多項式の理論が無いので、
V − 1 が (1 − t)(1 − t³) で割り切れること（ジョーンズの理論の既知の事実）と、V(i) = (−1)^Arf が実数で
あること（村上の結果）を、V の形と仮定 V(i) = V(−i) として置いた。三つ葉と 6₁ の多項式は表の値を入力として置いた。
形式化していないもの：次数の幅が広い結び目で六点のほかにも一致する点があること（下読みの AI が 5₂・5₁・
6₂・7₁ で計算した。機械では確かめていない）、両手型の結び目、絡み目（t^(1/2) の冪）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper928

open Polynomial Complex

/-- 六つの点を根にもつ多項式 W = (X − 1)³(X + 1)(X² + 1)(X² + X + 1)。 -/
noncomputable def W : ℂ[X] := (X - 1) ^ 3 * (X + 1) * (X ^ 2 + 1) * (X ^ 2 + X + 1)

/-- ジョーンズ多項式の値 V(t) = 1 + (t − 1)(t³ − 1)P(t)/t^M（V − 1 が (1 − t)(1 − t³) で割り切れる形）。 -/
noncomputable def V (M : ℕ) (P : ℂ[X]) (t : ℂ) : ℂ :=
  1 + (t - 1) * (t ^ 3 - 1) * P.eval t / t ^ M

/-- 鏡像との差の多項式 D = (X − 1)(X³ − 1)(P − reflect_N P)。 -/
noncomputable def D (N : ℕ) (P : ℂ[X]) : ℂ[X] := (X - 1) * (X ^ 3 - 1) * (P - reflect N P)

theorem eval_reflect {N : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ N) {t : ℂ} (ht : t ≠ 0) :
    (reflect N P).eval t = t ^ N * P.eval t⁻¹ := by
  have : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) t⁻¹ N P hP
  change (reflect N P).eval (⅟t⁻¹) * t⁻¹ ^ N = P.eval t⁻¹ at h
  rw [invOf_eq_inv, inv_inv] at h
  rw [← h, inv_pow]
  field_simp

/-- (1) D(t) = t^M(V(t) − V(1/t))（t ≠ 0）。 -/
theorem eval_D {M N : ℕ} {P : ℂ[X]} (hNM : N + 4 = 2 * M) (hP : P.natDegree ≤ N) {t : ℂ}
    (ht : t ≠ 0) : (D N P).eval t = t ^ M * (V M P t - V M P t⁻¹) := by
  unfold D V
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  rw [eval_reflect hP ht]
  have key : t ^ M * t ^ M = t ^ N * t ^ 4 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have htM : t ^ M ≠ 0 := pow_ne_zero _ ht
  have ht4 : t ^ 4 ≠ 0 := pow_ne_zero _ ht
  have hN : t ^ N = t ^ M * t ^ M / t ^ 4 := by rw [key]; field_simp
  generalize P.eval t⁻¹ = q
  generalize P.eval t = p
  rw [hN, inv_pow, inv_pow]
  field_simp
  ring

theorem N_even {M N : ℕ} (hNM : N + 4 = 2 * M) : Even N := ⟨M - 2, by omega⟩

/-- 四つの一次式の積 (X − 1)(X + 1)(X − i)(X + i) = (X − 1)(X + 1)(X² + 1)。 -/
theorem four_prod :
    (({1, -1, I, -I} : Multiset ℂ).map fun a => X - C a).prod =
      (X - 1) * (X + 1) * (X ^ 2 + 1) := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, map_one, map_neg]
  have h : (C I : ℂ[X]) * C I = -1 := by rw [← C_mul, I_mul_I, C_neg, C_1]
  linear_combination (-(X - 1) * (X + 1)) * h

theorem four_nodup : ({1, -1, I, -I} : Multiset ℂ).Nodup := by
  simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
    Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp [Complex.ext_iff] <;> norm_num

/-- (2) V(i) = V(−i) なら W ∣ D。 -/
theorem W_dvd_D {M N : ℕ} {P : ℂ[X]} (hNM : N + 4 = 2 * M) (hP : P.natDegree ≤ N)
    (hVi : V M P I = V M P (-I)) : W ∣ D N P := by
  set E := P - reflect N P with hEdef
  have hE1 : E.eval 1 = 0 := by
    simp only [E, eval_sub, eval_reflect hP one_ne_zero, one_pow, inv_one, one_mul, sub_self]
  have hEm1 : E.eval (-1) = 0 := by
    simp only [E, eval_sub, eval_reflect hP (neg_ne_zero.mpr one_ne_zero), (N_even hNM).neg_one_pow,
      one_mul, inv_neg, inv_one, sub_self]
  have hfac : ∀ t : ℂ, (D N P).eval t = (t - 1) * (t ^ 3 - 1) * E.eval t := by
    intro t; simp [D, E]
  have hEI : E.eval I = 0 := by
    have h1 := eval_D hNM hP I_ne_zero
    rw [inv_I, ← hVi, sub_self, mul_zero, hfac] at h1
    have hne : (I - 1) * (I ^ 3 - 1) ≠ 0 := by
      rw [show I ^ 3 = -I by linear_combination I * I_sq]
      apply mul_ne_zero <;> simp [Complex.ext_iff]
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hEmI : E.eval (-I) = 0 := by
    have h1 := eval_D hNM hP (neg_ne_zero.mpr I_ne_zero)
    rw [inv_neg, inv_I, neg_neg, hVi, sub_self, mul_zero, hfac] at h1
    have hne : (-I - 1) * ((-I) ^ 3 - 1) ≠ 0 := by
      rw [show (-I) ^ 3 = I by linear_combination (-I) * I_sq]
      apply mul_ne_zero <;> simp [Complex.ext_iff]
    exact (mul_eq_zero.mp h1).resolve_left hne
  -- (X − 1)(X + 1)(X² + 1) ∣ E
  have hF : (X - 1) * (X + 1) * (X ^ 2 + 1) ∣ E := by
    by_cases hE0 : E = 0
    · rw [hE0]; exact dvd_zero _
    · rw [← four_prod, Multiset.prod_X_sub_C_dvd_iff_le_roots hE0,
        Multiset.le_iff_subset four_nodup]
      intro a ha
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rw [mem_roots hE0, IsRoot.def]
      rcases ha with rfl | rfl | rfl | rfl
      · exact hE1
      · exact hEm1
      · exact hEI
      · exact hEmI
  obtain ⟨R, hR⟩ := hF
  refine ⟨R, ?_⟩
  unfold D W
  rw [← hEdef, hR]
  ring

/-- (2) 係数が実数で V(i) が実数なら V(i) = V(−i)。 -/
theorem Vi_eq_of_real {M : ℕ} {P : ℂ[X]} (hreal : ∀ n, (P.coeff n).im = 0)
    (hVi : (V M P I).im = 0) : V M P I = V M P (-I) := by
  have hconj : ∀ z : ℂ, P.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.eval z) := by
    intro z
    rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_mul, map_pow, conj_eq_iff_im.mpr (hreal n)]
  have hV : V M P (-I) = (starRingEnd ℂ) (V M P I) := by
    unfold V
    rw [← conj_I, hconj]
    simp only [map_add, map_one, map_mul, map_div₀, map_sub, map_pow]
  rw [hV, conj_eq_iff_im.mpr hVi]

/-- ω = −1/2 + (√3/2)i と ω² = −1/2 − (√3/2)i。 -/
noncomputable def ω : ℂ := -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I
noncomputable def ω' : ℂ := -1 / 2 - (Real.sqrt 3 / 2 : ℝ) * I

theorem quad_factor (t : ℂ) : t ^ 2 + t + 1 = (t - ω) * (t - ω') := by
  unfold ω ω'
  have h3 : ((Real.sqrt 3 / 2 : ℝ) : ℂ) ^ 2 = 3 / 4 := by
    rw [← ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; push_cast; norm_num
  linear_combination I ^ 2 * h3 + (3 / 4 : ℂ) * I_sq

/-- (3) W(t) = 0 ⇔ t は六点のどれか。 -/
theorem eval_W_eq_zero_iff (t : ℂ) :
    W.eval t = 0 ↔ t = 1 ∨ t = -1 ∨ t = I ∨ t = -I ∨ t = ω ∨ t = ω' := by
  have e : W.eval t = (t - 1) ^ 3 * (t + 1) * ((t - I) * (t + I)) * ((t - ω) * (t - ω')) := by
    unfold W
    simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_one]
    rw [← quad_factor]
    have : (t - I) * (t + I) = t ^ 2 + 1 := by rw [← sub_eq_zero]; ring_nf; rw [I_sq]; ring
    rw [this]
  rw [e]
  simp only [mul_eq_zero, pow_eq_zero_iff (n := 3) (by norm_num), sub_eq_zero,
    add_eq_zero_iff_eq_neg]
  tauto

theorem natDegree_W : W.natDegree = 8 := by
  unfold W
  compute_degree!

theorem W_ne_zero : W ≠ 0 := by
  intro h
  have := natDegree_W
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

theorem natDegree_D_le {N : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ N) : (D N P).natDegree ≤ 4 + N := by
  unfold D
  have h1 : ((X - 1) * (X ^ 3 - 1) : ℂ[X]).natDegree ≤ 4 := by compute_degree
  have h2 : (P - reflect N P).natDegree ≤ N := by
    apply (natDegree_sub_le _ _).trans
    apply max_le hP
    apply natDegree_reflect_le.trans
    exact max_le le_rfl hP
  exact (natDegree_mul_le).trans (add_le_add h1 h2)

/-- (4) M ≤ 4 で D ≠ 0 なら、V(t) = V(1/t) ⇔ t は六点のどれか（t ≠ 0）。 -/
theorem six_points {M N : ℕ} {P : ℂ[X]} (hNM : N + 4 = 2 * M) (hP : P.natDegree ≤ N)
    (hVi : V M P I = V M P (-I)) (hM : M ≤ 4) (hD : D N P ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    V M P t = V M P t⁻¹ ↔ t = 1 ∨ t = -1 ∨ t = I ∨ t = -I ∨ t = ω ∨ t = ω' := by
  obtain ⟨R, hR⟩ := W_dvd_D hNM hP hVi
  have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hD hR
  have hdeg : (D N P).natDegree = 8 + R.natDegree := by
    rw [hR, natDegree_mul W_ne_zero hR0, natDegree_W]
  have hle := natDegree_D_le (N := N) hP
  have hR0' : R.natDegree = 0 := by omega
  have hc : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero hR0'
  have hc0 : R.coeff 0 ≠ 0 := by
    intro h; apply hR0; rw [hc, h, C_0]
  rw [← eval_W_eq_zero_iff]
  have hev := eval_D hNM hP ht
  rw [hR, hc, eval_mul, eval_C] at hev
  have htM : t ^ M ≠ 0 := pow_ne_zero _ ht
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at hev
    exact (mul_eq_zero.mp hev).resolve_right hc0
  · intro h
    rw [h, zero_mul] at hev
    have := (mul_eq_zero.mp hev.symm).resolve_left htM
    exact (sub_eq_zero.mp this)

/-- (4) M ≤ 3 なら、すべての t ≠ 0 で V(t) = V(1/t)。 -/
theorem symmetric_of_small {M N : ℕ} {P : ℂ[X]} (hNM : N + 4 = 2 * M) (hP : P.natDegree ≤ N)
    (hVi : V M P I = V M P (-I)) (hM : M ≤ 3) {t : ℂ} (ht : t ≠ 0) : V M P t = V M P t⁻¹ := by
  have hD : D N P = 0 := by
    by_contra hD
    have h1 := natDegree_le_of_dvd (W_dvd_D hNM hP hVi) hD
    have h2 := natDegree_D_le (N := N) hP
    rw [natDegree_W] at h1
    omega
  have hev := eval_D hNM hP ht
  rw [hD, eval_zero] at hev
  have := (mul_eq_zero.mp hev.symm).resolve_left (pow_ne_zero _ ht)
  exact sub_eq_zero.mp this

/-! ### 三つ葉と 6₁ -/

/-- (5) 右手の三つ葉：P = −X⁴、M = 4 で V = t + t³ − t⁴。 -/
theorem trefoil_V {t : ℂ} (ht : t ≠ 0) : V 4 (-X ^ 4) t = t + t ^ 3 - t ^ 4 := by
  unfold V
  simp only [eval_neg, eval_pow, eval_X]
  field_simp
  ring

/-- (5) 三つ葉では D = −W。 -/
theorem trefoil_D : D 4 (-X ^ 4) = -W := by
  unfold D W
  rw [reflect_neg, reflect_monomial, revAt_le (le_refl 4), Nat.sub_self, pow_zero]
  ring

/-- (5) 6₁：P = X² + 1、M = 4 で V = t⁻⁴ − t⁻³ + t⁻² − 2t⁻¹ + 2 − t + t²。 -/
theorem knot61_V {t : ℂ} (ht : t ≠ 0) :
    V 4 (X ^ 2 + 1) t = t⁻¹ ^ 4 - t⁻¹ ^ 3 + t⁻¹ ^ 2 - 2 * t⁻¹ + 2 - t + t ^ 2 := by
  unfold V
  simp only [eval_add, eval_pow, eval_X, eval_one]
  field_simp
  ring

/-- (5) 6₁ でも D = −W。 -/
theorem knot61_D : D 4 (X ^ 2 + 1) = -W := by
  unfold D W
  rw [reflect_add, reflect_monomial, revAt_le (by norm_num : 2 ≤ 4),
    show (1 : ℂ[X]) = C 1 from C_1.symm, reflect_C, C_1]
  norm_num
  ring

/-- (5) 三つ葉では V(t) = V(1/t) ⇔ t は六点のどれか（t ≠ 0）。 -/
theorem trefoil_six_points {t : ℂ} (ht : t ≠ 0) :
    V 4 (-X ^ 4) t = V 4 (-X ^ 4) t⁻¹ ↔
      t = 1 ∨ t = -1 ∨ t = I ∨ t = -I ∨ t = ω ∨ t = ω' := by
  have hP : (-X ^ 4 : ℂ[X]).natDegree ≤ 4 := by compute_degree
  have hev := eval_D (M := 4) (N := 4) (by norm_num) hP ht
  rw [trefoil_D, eval_neg] at hev
  rw [← eval_W_eq_zero_iff]
  have ht4 : t ^ 4 ≠ 0 := pow_ne_zero _ ht
  constructor
  · intro h
    rw [h, sub_self, mul_zero, neg_eq_zero] at hev
    exact hev
  · intro h
    rw [h, neg_zero] at hev
    have := (mul_eq_zero.mp hev.symm).resolve_left ht4
    exact sub_eq_zero.mp this

end Paper928

end Yamagishi
