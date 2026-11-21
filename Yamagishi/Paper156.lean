/-
論文156『球殻の内部が定数なのは、平均値定理のためではない』の芯の一つを、一般の次元で機械に確かめさせる（格上げ）。

原稿（156_yamagishi_not_the_mean_value_theorem/…_jp.tex）が示している事：
  検算3.1：d 次元の球対称な調和関数は f'' + (d−1)/r · f' = 0 を満たし、d = 3, 4, 5, 6 の表で
  C₁ + C₂ r^(2−d) の形になる（「いずれも A + B r^(2−d) の形である（証明終）」）。
  観察3.2：原点を含む領域で有界であることが B = 0 を強制し、残るのは定数である。
  d = 2 の log の形は表に無い。

ここで証明した一般の言明（d は任意の実数、r > 0 の上で）：
  (1) f'' + (d−1)/r · f' = 0 の解は、d ≠ 2 なら f = A + B r^(2−d)、d = 2 なら f = A + B log r。
      逆に、この形はどれも方程式を満たす。
  (2) d ≥ 2 で f が原点の近く（0 < r < 1）で有界なら B = 0、つまり f は定数。
  (3) d < 2 では (2) は成り立たない：d = 1 の f(r) = r は方程式を満たし、有界で、定数でない
      （1 < d < 2 でも r^(2−d) は有界で定数でない）。
足した仮定・条件：(2) には d ≥ 2 が要る（原稿の表は d = 3〜6 で、この条件の内側にある）。
「球対称な調和関数」は、動径 r だけの関数 f が上の常微分方程式を満たすこととして置いた
（d 次元のラプラシアンの球対称な形が f'' + (d−1)f'/r であることは、形式化の外の入力）。
f は r > 0 で二回微分できるとし、導関数を f'・f'' と名付けて仮定に置いた。

形式化していないもの：Φ = z の反例（検算2.1）、最大値原理（観察3.3）、核 r^(2−d) の数値積分
（検算4.1・5.1）、論文51・01 との読み（第6節）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper156

open Real Set

/-- r > 0 で微分が 0 なら、r > 0 で一定。 -/
theorem const_on_pos (φ : ℝ → ℝ) (h : ∀ r, 0 < r → HasDerivAt φ 0 r) : ∀ r, 0 < r → φ r = φ 1 := by
  intro r hr
  have key : ∀ a b, 0 < a → a ≤ b → φ b = φ a := by
    intro a b ha hab
    have hcont : ContinuousOn φ (Icc a b) := fun t ht =>
      (h t (by linarith [ht.1])).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun t ht => (h t (by linarith [ht.1])).hasDerivWithinAt) b ⟨hab, le_refl b⟩
  rcases le_total 1 r with h1 | h1
  · exact key 1 r one_pos h1
  · exact (key r 1 hr h1).symm

/-- (1) 第一段：r^(d−1) f'(r) は一定。 -/
theorem flux_const (d : ℝ) (f' f'' : ℝ → ℝ)
    (hf' : ∀ r, 0 < r → HasDerivAt f' (f'' r) r)
    (hode : ∀ r, 0 < r → f'' r + (d - 1) / r * f' r = 0) :
    ∀ r, 0 < r → r ^ (d - 1) * f' r = f' 1 := by
  have h := const_on_pos (fun r => r ^ (d - 1) * f' r) ?_
  · intro r hr
    have := h r hr
    simpa using this
  intro r hr
  have h1 : HasDerivAt (fun r => r ^ (d - 1)) ((d - 1) * r ^ (d - 1 - 1)) r :=
    hasDerivAt_rpow_const (Or.inl hr.ne')
  have h2 := h1.mul (hf' r hr)
  convert h2 using 1
  have e : r ^ (d - 1 - 1) = r ^ (d - 1) / r := by
    rw [rpow_sub hr, rpow_one]
  rw [e]
  have := hode r hr
  field_simp
  field_simp at this
  linear_combination (-(r ^ (d - 1))) * this

/-- (1) 一般解（d ≠ 2）：f = A + B r^(2−d)。 -/
theorem radial_solution (d : ℝ) (hd : d ≠ 2) (f f' f'' : ℝ → ℝ)
    (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r) (hf' : ∀ r, 0 < r → HasDerivAt f' (f'' r) r)
    (hode : ∀ r, 0 < r → f'' r + (d - 1) / r * f' r = 0) :
    ∃ A B : ℝ, ∀ r, 0 < r → f r = A + B * r ^ (2 - d) := by
  have hflux := flux_const d f' f'' hf' hode
  have h2d : (2 - d) ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
  set B := f' 1 / (2 - d)
  have hφ : ∀ r, 0 < r → HasDerivAt (fun r => f r - B * r ^ (2 - d)) 0 r := by
    intro r hr
    have h1 : HasDerivAt (fun r => r ^ (2 - d)) ((2 - d) * r ^ (2 - d - 1)) r :=
      hasDerivAt_rpow_const (Or.inl hr.ne')
    have h2 := (hf r hr).sub (h1.const_mul B)
    convert h2 using 1
    have hfl := hflux r hr
    have e : r ^ (2 - d - 1) * r ^ (d - 1) = 1 := by
      rw [← rpow_add hr, show (2 - d - 1 + (d - 1)) = 0 by ring, rpow_zero]
    have hfr : f' r = f' 1 * r ^ (2 - d - 1) := by
      have : f' r = f' r * (r ^ (2 - d - 1) * r ^ (d - 1)) := by rw [e, mul_one]
      rw [this]; linear_combination (r ^ (2 - d - 1)) * hfl
    rw [hfr]
    simp only [B]
    field_simp
    ring
  refine ⟨f 1 - B * 1 ^ (2 - d), B, fun r hr => ?_⟩
  have := const_on_pos _ hφ r hr
  linarith

/-- (1) 一般解（d = 2）：f = A + B log r。 -/
theorem radial_solution_two (f f' f'' : ℝ → ℝ)
    (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r) (hf' : ∀ r, 0 < r → HasDerivAt f' (f'' r) r)
    (hode : ∀ r, 0 < r → f'' r + (2 - 1) / r * f' r = 0) :
    ∃ A B : ℝ, ∀ r, 0 < r → f r = A + B * log r := by
  have hflux := flux_const 2 f' f'' hf' hode
  set B := f' 1
  have hφ : ∀ r, 0 < r → HasDerivAt (fun r => f r - B * log r) 0 r := by
    intro r hr
    have h2 := (hf r hr).sub ((hasDerivAt_log hr.ne').const_mul B)
    convert h2 using 1
    have hfl := hflux r hr
    norm_num at hfl
    simp only [B]
    field_simp
    linarith
  refine ⟨f 1, B, fun r hr => ?_⟩
  have := const_on_pos _ hφ r hr
  simp only [log_one, mul_zero, sub_zero] at this
  linarith

/-- (1) 逆向き：A + B r^(2−d) は方程式を満たす（すべての d）。 -/
theorem power_form_solves (d A B r : ℝ) (hr : 0 < r) :
    let f' := fun r : ℝ => B * ((2 - d) * r ^ (1 - d))
    let f'' := fun r : ℝ => B * ((2 - d) * ((1 - d) * r ^ (-d)))
    HasDerivAt (fun r => A + B * r ^ (2 - d)) (f' r) r ∧ HasDerivAt f' (f'' r) r ∧
      f'' r + (d - 1) / r * f' r = 0 := by
  intro f' f''
  have h1 : HasDerivAt (fun r : ℝ => r ^ (2 - d)) ((2 - d) * r ^ (2 - d - 1)) r :=
    hasDerivAt_rpow_const (Or.inl hr.ne')
  have h2 : HasDerivAt (fun r : ℝ => r ^ (1 - d)) ((1 - d) * r ^ (1 - d - 1)) r :=
    hasDerivAt_rpow_const (Or.inl hr.ne')
  refine ⟨?_, ?_, ?_⟩
  · have := (h1.const_mul B).const_add A
    convert this using 1
    simp only [f']; congr 2; ring_nf
  · have := (h2.const_mul (2 - d)).const_mul B
    convert this using 1
    simp only [f'']; congr 3; ring_nf
  · simp only [f', f'']
    have e : r ^ (1 - d) = r * r ^ (-d) := by
      rw [show (1 - d) = 1 + (-d) by ring, rpow_add hr, rpow_one]
    rw [e]
    field_simp
    ring

/-- (2) d > 2：原点の近くで有界なら B = 0。 -/
theorem bounded_forces_B_zero (d A B M : ℝ) (hd : 2 < d)
    (hbd : ∀ r, 0 < r → r < 1 → |A + B * r ^ (2 - d)| ≤ M) : B = 0 := by
  by_contra hB
  have hBpos : 0 < |B| := abs_pos.mpr hB
  set K := (M + |A|) / |B| + 2
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd (1 / 2) (by norm_num) (by norm_num))
  have hK : 1 < K := by
    have : 0 ≤ (M + |A|) / |B| := div_nonneg (by positivity) hBpos.le
    linarith
  have hneg : 1 / (2 - d) < 0 := by
    apply div_neg_of_pos_of_neg one_pos; linarith
  set r := K ^ (1 / (2 - d))
  have hr0 : 0 < r := rpow_pos_of_pos (by linarith) _
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg hK hneg
  have hrK : r ^ (2 - d) = K := by
    simp only [r]
    rw [← rpow_mul (by linarith), one_div_mul_cancel (by linarith), rpow_one]
  have h := hbd r hr0 hr1
  rw [hrK] at h
  have h2 : |B| * K ≤ M + |A| := by
    have : |B * K| ≤ |A + B * K| + |A| := by
      have := abs_add_le (A + B * K) (-A)
      rw [show A + B * K + -A = B * K by ring, abs_neg] at this
      exact this
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < K)] at this
    linarith
  have h3 : |B| * K = M + |A| + 2 * |B| := by
    simp only [K]; field_simp
  linarith

/-- (2) d = 2：原点の近くで有界なら B = 0（log の形）。 -/
theorem bounded_forces_B_zero_two (A B M : ℝ)
    (hbd : ∀ r, 0 < r → r < 1 → |A + B * log r| ≤ M) : B = 0 := by
  by_contra hB
  have hBpos : 0 < |B| := abs_pos.mpr hB
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd (1 / 2) (by norm_num) (by norm_num))
  set K := (M + |A|) / |B| + 2
  have hK : 0 < K := by
    have : 0 ≤ (M + |A|) / |B| := div_nonneg (by positivity) hBpos.le
    linarith
  set r := exp (-K)
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := hbd r hr0 hr1
  simp only [r, log_exp] at h
  have h2 : |B| * K ≤ M + |A| := by
    have h4 : |B * (-K)| ≤ |A + B * (-K)| + |A| := by
      have := abs_add_le (A + B * (-K)) (-A)
      rw [show A + B * (-K) + -A = B * (-K) by ring, abs_neg] at this
      exact this
    rw [abs_mul, abs_neg, abs_of_pos hK] at h4
    linarith
  have h3 : |B| * K = M + |A| + 2 * |B| := by
    simp only [K]; field_simp
  linarith

/-- (2) まとめ：d ≥ 2 で、球対称な調和関数が原点の近くで有界なら、r > 0 で定数。 -/
theorem bounded_radial_harmonic_const (d : ℝ) (hd : 2 ≤ d) (f f' f'' : ℝ → ℝ)
    (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r) (hf' : ∀ r, 0 < r → HasDerivAt f' (f'' r) r)
    (hode : ∀ r, 0 < r → f'' r + (d - 1) / r * f' r = 0)
    (M : ℝ) (hbd : ∀ r, 0 < r → r < 1 → |f r| ≤ M) :
    ∀ r, 0 < r → f r = f 1 := by
  rcases hd.lt_or_eq with hd2 | hd2
  · obtain ⟨A, B, hAB⟩ := radial_solution d hd2.ne' f f' f'' hf hf' hode
    have hB : B = 0 := bounded_forces_B_zero d A B M hd2
      (fun r h0 h1 => by rw [← hAB r h0]; exact hbd r h0 h1)
    intro r hr
    rw [hAB r hr, hAB 1 one_pos, hB]; ring
  · subst hd2
    obtain ⟨A, B, hAB⟩ := radial_solution_two f f' f'' hf hf' hode
    have hB : B = 0 := bounded_forces_B_zero_two A B M
      (fun r h0 h1 => by rw [← hAB r h0]; exact hbd r h0 h1)
    intro r hr
    rw [hAB r hr, hAB 1 one_pos, hB]; ring

/-- (3) d ≥ 2 の条件は外せない：d = 1 で f(r) = r は方程式を満たし、0 < r < 1 で有界、定数でない。 -/
theorem d_one_counterexample :
    (∀ r : ℝ, 0 < r → HasDerivAt (fun r : ℝ => r) 1 r) ∧
    (∀ r : ℝ, 0 < r → HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r) ∧
    (∀ r : ℝ, 0 < r → (0 : ℝ) + ((1 : ℝ) - 1) / r * 1 = 0) ∧
    (∀ r : ℝ, 0 < r → r < 1 → |r| ≤ 1) ∧ (1 / 2 : ℝ) ≠ 1 := by
  refine ⟨fun r _ => hasDerivAt_id' r, fun r _ => hasDerivAt_const r 1, fun r _ => by ring,
    fun r h0 h1 => by rw [abs_of_pos h0]; linarith, by norm_num⟩

end Paper156

end Yamagishi
