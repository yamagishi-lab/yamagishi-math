/-
論文346『三つの次数のうち二つでは、半減期は物質の性質ではない』を、一般の n 次の反応へ広げて
機械に確かめさせる（格上げ）。

原稿（346_yamagishi_for_two_of_three_orders_half_life_is_not_a_property/…_jp.tex）が示している事：
  0 次・1 次・2 次の三つの速度式 −dC/dt = k、kC、kC² の半減期 C₀/(2k)、ln2/k、1/(kC₀) を表に並べ
  （式は教科書のものを引く）、k = 0.1 の数値で、初濃度を 4 倍にすると 0 次は 4 倍・2 次は 1/4、
  一つの試料の中で連続する半減期は 0 次で半分ずつ、2 次で倍ずつになることを示す。
  一般の n 次は扱わない（射程で明記）。

ここで証明した一般の言明（n は任意の実数、k > 0、C₀ > 0）：
  (1) −dC/dt = k C^n の解が正のまま C₀ から C₀/2 に達したなら、その時刻は
      t½ = (2^(n−1) − 1) C₀^(1−n) / ((n − 1) k)（n ≠ 1）、ln 2 / k（n = 1）。
      微分方程式から直接に導いた（解の公式を仮定していない）。
  (2) その解は実際にある（解を具体的に書き、方程式を満たし、t½ で C₀/2 になることを示した）。
  (3) 半減期が初濃度によらない ⇔ n = 1。
  (4) 一つの試料の中で、次の半減期は前の半減期の 2^(n−1) 倍（0 次で 1/2、1 次で 1、2 次で 2）。

足した仮定：速度定数 k > 0、初濃度 C₀ > 0、濃度は半減期に達するまで正（C > 0）。
「微分できる」は、区間 [0, τ] のすべての点での両側の微分として置いた（端点を含む）。
形式化していないもの：放射性崩壊・薬物の消失などの例、「物質の性質か状態の性質か」という読み、
k = 0.1 の数表の値そのもの（式に値を入れたもの）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper346

open Real Set

/-- n 次の反応の半減期の式。 -/
noncomputable def halfLife (n k C0 : ℝ) : ℝ :=
  if n = 1 then log 2 / k else (2 ^ (n - 1) - 1) * C0 ^ (1 - n) / ((n - 1) * k)

/-- (C₀/2)^(1−n) = C₀^(1−n) · 2^(n−1)。 -/
theorem half_rpow (C0 n : ℝ) (hC0 : 0 < C0) : (C0 / 2) ^ (1 - n) = C0 ^ (1 - n) * 2 ^ (n - 1) := by
  rw [div_rpow hC0.le (by norm_num), div_eq_mul_inv, ← rpow_neg (by norm_num)]
  congr 2; ring

/-- (1) 微分方程式から半減期を導く：解が [0, τ] で正、C(0) = C₀、C(τ) = C₀/2 なら τ = t½。 -/
theorem halfLife_of_ode (n k C0 τ : ℝ) (C : ℝ → ℝ) (hk : 0 < k) (hC0 : 0 < C0) (hτ : 0 ≤ τ)
    (hpos : ∀ t ∈ Icc 0 τ, 0 < C t)
    (hode : ∀ t ∈ Icc 0 τ, HasDerivAt C (-(k * C t ^ n)) t)
    (h0 : C 0 = C0) (hhalf : C τ = C0 / 2) : τ = halfLife n k C0 := by
  unfold halfLife
  split_ifs with hn
  · -- n = 1：log C + k t は一定
    subst hn
    set φ : ℝ → ℝ := fun t => log (C t) + k * t
    have hφ : ∀ t ∈ Icc 0 τ, HasDerivAt φ 0 t := by
      intro t ht
      have h1 := (hode t ht).log (hpos t ht).ne'
      have h2 := h1.add ((hasDerivAt_id' t).const_mul k)
      convert h2 using 1
      rw [rpow_one]
      field_simp [(hpos t ht).ne']
      ring
    have hcont : ContinuousOn φ (Icc 0 τ) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
    have hc := constant_of_has_deriv_right_zero hcont
      (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) τ ⟨hτ, le_refl τ⟩
    simp only [φ, h0, hhalf, mul_zero, add_zero] at hc
    rw [log_div hC0.ne' (by norm_num)] at hc
    field_simp
    linarith
  · -- n ≠ 1：C^(1−n) − (n−1) k t は一定
    set φ : ℝ → ℝ := fun t => C t ^ (1 - n) - (n - 1) * k * t
    have hφ : ∀ t ∈ Icc 0 τ, HasDerivAt φ 0 t := by
      intro t ht
      have hCt := hpos t ht
      have h1 := (hode t ht).rpow_const (p := 1 - n) (Or.inl hCt.ne')
      have h2 := h1.sub ((hasDerivAt_id' t).const_mul ((n - 1) * k))
      convert h2 using 1
      have : C t ^ n * C t ^ (1 - n - 1) = 1 := by
        rw [← rpow_add hCt]; simp
      linear_combination (k * (1 - n)) * this
    have hcont : ContinuousOn φ (Icc 0 τ) := fun t ht => (hφ t ht).continuousAt.continuousWithinAt
    have hc := constant_of_has_deriv_right_zero hcont
      (fun t ht => (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) τ ⟨hτ, le_refl τ⟩
    simp only [φ, h0, hhalf, mul_zero, sub_zero] at hc
    rw [half_rpow C0 n hC0] at hc
    have hn' : n - 1 ≠ 0 := sub_ne_zero.mpr hn
    field_simp
    linarith

/-- (2) 解は実際にある（n ≠ 1）：C(t) = (C₀^(1−n) + (n−1) k t)^(1/(1−n)) は [0, t½] で正、
方程式を満たし、C(0) = C₀、C(t½) = C₀/2。 -/
theorem solution_exists (n k C0 : ℝ) (hn : n ≠ 1) (hk : 0 < k) (hC0 : 0 < C0) :
    let C : ℝ → ℝ := fun t => (C0 ^ (1 - n) + (n - 1) * k * t) ^ (1 / (1 - n))
    0 ≤ halfLife n k C0 ∧ C 0 = C0 ∧ C (halfLife n k C0) = C0 / 2 ∧
    (∀ t ∈ Icc 0 (halfLife n k C0), 0 < C t ∧ HasDerivAt C (-(k * C t ^ n)) t) := by
  intro C
  have hn1 : 1 - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hn2 : n - 1 ≠ 0 := sub_ne_zero.mpr hn
  have hA : 0 < C0 ^ (1 - n) := rpow_pos_of_pos hC0 _
  have hB : 0 < (C0 / 2) ^ (1 - n) := rpow_pos_of_pos (by positivity) _
  -- 半減期での底は (C₀/2)^(1−n)
  have hbase : C0 ^ (1 - n) + (n - 1) * k * halfLife n k C0 = (C0 / 2) ^ (1 - n) := by
    unfold halfLife; rw [ite_eq_right hn, half_rpow C0 n hC0]; field_simp; ring
  have hroot : ∀ x : ℝ, 0 < x → (x ^ (1 - n)) ^ (1 / (1 - n)) = x := by
    intro x hx
    rw [← rpow_mul hx.le, mul_one_div_cancel hn1, rpow_one]
  -- 底は区間の両端で正、途中は一次式なので正
  have hbasepos : ∀ t ∈ Icc 0 (halfLife n k C0), 0 < C0 ^ (1 - n) + (n - 1) * k * t := by
    intro t ht
    have hT : 0 ≤ halfLife n k C0 := ht.1.trans ht.2
    rcases le_total 0 ((n - 1) * k) with h | h
    · have := mul_nonneg h ht.1; linarith
    · have h1 : (n - 1) * k * halfLife n k C0 ≤ (n - 1) * k * t :=
        mul_le_mul_of_nonpos_left ht.2 h
      linarith
  have hT : 0 ≤ halfLife n k C0 := by
    unfold halfLife; rw [ite_eq_right hn]
    rcases lt_or_gt_of_ne hn with h | h
    · have h2 : (2 : ℝ) ^ (n - 1) < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      apply div_nonneg_of_nonpos
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hk.le
    · have h2 : (1 : ℝ) < 2 ^ (n - 1) := one_lt_rpow (by norm_num) (by linarith)
      apply div_nonneg
      · exact mul_nonneg (by linarith) hA.le
      · exact mul_nonneg (by linarith) hk.le
  refine ⟨hT, ?_, ?_, ?_⟩
  · simp only [C, mul_zero, add_zero]; exact hroot C0 hC0
  · simp only [C]; rw [hbase]; exact hroot _ (by positivity)
  · intro t ht
    have hb := hbasepos t ht
    refine ⟨rpow_pos_of_pos hb _, ?_⟩
    have hlin : HasDerivAt (fun t => C0 ^ (1 - n) + (n - 1) * k * t) ((n - 1) * k) t := by
      simpa using ((hasDerivAt_id t).const_mul ((n - 1) * k)).const_add (C0 ^ (1 - n))
    have h := hlin.rpow_const (p := 1 / (1 - n)) (Or.inl hb.ne')
    convert h using 1
    simp only [C]
    rw [← rpow_mul hb.le]
    have e : 1 / (1 - n) - 1 = 1 / (1 - n) * n := by field_simp; ring
    rw [e]
    field_simp
    ring

/-- 原稿の表の三つ：0 次 C₀/(2k)、1 次 ln2/k、2 次 1/(kC₀)。 -/
theorem table_three_orders (k C0 : ℝ) (hk : 0 < k) (hC0 : 0 < C0) :
    halfLife 0 k C0 = C0 / (2 * k) ∧ halfLife 1 k C0 = log 2 / k ∧
    halfLife 2 k C0 = 1 / (k * C0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold halfLife; rw [ite_eq_right (by norm_num)]
    norm_num [rpow_neg_one]
    field_simp
  · unfold halfLife; rw [ite_eq_left rfl]
  · unfold halfLife; rw [ite_eq_right (by norm_num)]
    norm_num [rpow_neg_one]
    field_simp

/-- 2^x = 1 となるのは x = 0 のときだけ。 -/
theorem two_rpow_ne_one (x : ℝ) (hx : x ≠ 0) : (2 : ℝ) ^ x ≠ 1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact (rpow_lt_one_of_one_lt_of_neg (by norm_num) h).ne
  · exact (one_lt_rpow (by norm_num) h).ne'

/-- (3) 半減期が初濃度によらない（すべての正の C₀, C₀' で同じ）⇔ n = 1。 -/
theorem halfLife_independent_iff (n k : ℝ) (hk : 0 < k) :
    (∀ C0 C0' : ℝ, 0 < C0 → 0 < C0' → halfLife n k C0 = halfLife n k C0') ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn
    have h12 := h 1 2 one_pos two_pos
    unfold halfLife at h12
    rw [ite_eq_right hn, ite_eq_right hn, one_rpow] at h12
    have hn1 : n - 1 ≠ 0 := sub_ne_zero.mpr hn
    have hA : (2 : ℝ) ^ (n - 1) - 1 ≠ 0 := sub_ne_zero.mpr (two_rpow_ne_one _ hn1)
    have hB : (2 : ℝ) ^ (1 - n) ≠ 1 := two_rpow_ne_one _ (by intro h0; exact hn1 (by linarith))
    have hk' : (n - 1) * k ≠ 0 := mul_ne_zero hn1 hk.ne'
    field_simp at h12
    exact hB h12.symm
  · rintro rfl C0 C0' _ _
    simp [halfLife]

/-- (4) 一つの試料の中で、次の半減期（C₀/2 から C₀/4 まで）は前の半減期の 2^(n−1) 倍。
0 次で 1/2、1 次で 1、2 次で 2（原稿の検算 3.1 の「半分ずつ」「倍ずつ」）。 -/
theorem successive_ratio (n k C0 : ℝ) (hC0 : 0 < C0) :
    halfLife n k (C0 / 2) = 2 ^ (n - 1) * halfLife n k C0 := by
  unfold halfLife
  split_ifs with hn
  · subst hn; simp
  · rw [half_rpow C0 n hC0]; ring

theorem successive_ratio_three :
    (2 : ℝ) ^ ((0 : ℝ) - 1) = 1 / 2 ∧ (2 : ℝ) ^ ((1 : ℝ) - 1) = 1 ∧
      (2 : ℝ) ^ ((2 : ℝ) - 1) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rpow_neg_one]

end Paper346

end Yamagishi
