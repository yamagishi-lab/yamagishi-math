/-
論文582『倍音の並びを決めるのは、閉じた端ではなく、そこからの管の広がり方である』の格上げ（一般の形）。

日本語：a > 0 で tan z = −az の正の根 z_k(a) は区間 ((2k − 1)π/2, kπ) にただ一つずつあり、a について
狭義に減る。m > n なら比 z_m/z_n は a について狭義に増え、a → 0 で m/n、a → ∞ で (2m − 1)/(2n − 1)
に近づく。とくに第二の共鳴と基音の比は 2 から 3 へ狭義に単調に動く。
English: For a > 0 the equation tan z = −az has exactly one root z_k(a) in ((2k − 1)π/2, kπ); it
decreases strictly in a, and for m > n the ratio z_m/z_n increases strictly from m/n (a → 0) to
(2m − 1)/(2n − 1) (a → ∞); in particular z₂/z₁ moves monotonically from 2 to 3.

原稿（582_yamagishi_the_widening_not_the_closed_end/…_jp.tex）は、円錐台の共鳴の式 tan kL = −kx₀ を
x₀/L = 0.05・0.1・0.3・1・3 で解き、最初の二根と比、x₀/L = 10⁶ と x₀ → 0 の極限を二分法で示す。
単調性は表から読むだけ。

ここで証明した言明（a = x₀/L、z = kL。理想の管の模型の式 tan z = −az を出発点に置いた）：
  (1) `exists_root`・`root_spec`・`root_unique`：k ≥ 1、a > 0 で、区間 I_k = ((2k − 1)π/2, kπ) に
      tan z = −az の根はちょうど一つ（`root k a`）。
  (2) `root_strictAntiOn`：z_k(a) は a について狭義に減る。
  (3) `ratio_strictMonoOn`：1 ≤ n < m なら z_m/z_n は a について狭義に増える。
  (4) `root_tendsto_zero`・`root_tendsto_atTop`：a → 0+ で z_k → kπ、a → ∞ で z_k → (2k − 1)π/2。
      `ratio_tendsto_zero`・`ratio_tendsto_atTop`：比は m/n と (2m − 1)/(2n − 1) に近づく。
      `second_over_first`：z₂/z₁ は 2 から 3 へ狭義に増える（原稿の場合）。
証明の筋：A(z) = −tan z/z と置くと z·A′(z) = −(1 + A + A²z²)。λ > 1 で A(λt) と A(t) が等しい点では
A(λt) の傾きのほうが小さいので、二つの枝の曲線は一度しか交わらない（Mathlib の比較の定理
`image_le_of_deriv_right_lt_deriv_boundary'`）。下読みの AI の筋（陰関数の微分 dz/da）とは別の道。
形式化していないもの：tan kL = −kx₀ を円錐台の波動方程式から出す所、損失・開口補正、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper582

open Real Set Filter Topology

/-! ### 枝と関数 A -/

/-- 第 k の根の区間 I_k = ((2k − 1)π/2, kπ)。 -/
noncomputable def I (k : ℕ) : Set ℝ := Ioo ((2 * k - 1) * π / 2) (k * π)

/-- A(z) = −tan z/z（tan z = −az ⇔ A(z) = a）。 -/
noncomputable def A (z : ℝ) : ℝ := -tan z / z

theorem I_pos {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : z ∈ I k) : 0 < z := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : π / 2 ≤ (2 * k - 1) * π / 2 := by nlinarith [pi_pos]
  linarith [hz.1, pi_pos]

/-- z ∈ I_k ⇔ w = kπ − z ∈ (0, π/2)。 -/
theorem w_mem {k : ℕ} {z : ℝ} (hz : z ∈ I k) : k * π - z ∈ Ioo 0 (π / 2) := by
  obtain ⟨h1, h2⟩ := hz
  constructor <;> linarith

theorem tan_eq_neg {k : ℕ} (z : ℝ) : tan z = -tan (k * π - z) := by
  have hs : sin (k * π - z) = -((-1) ^ k * sin z) := by
    rw [sin_sub, cos_nat_mul_pi, sin_nat_mul_pi]
    ring
  have hc : cos (k * π - z) = (-1) ^ k * cos z := by
    rw [cos_sub, cos_nat_mul_pi, sin_nat_mul_pi]; ring
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, hs, hc]
  have : ((-1 : ℝ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases h0 : cos z = 0
  · simp [h0]
  · field_simp

theorem cos_ne_zero_of_mem {k : ℕ} {z : ℝ} (hz : z ∈ I k) : cos z ≠ 0 := by
  have hw := w_mem hz
  have hc : cos (k * π - z) = (-1) ^ k * cos z := by
    rw [cos_sub, cos_nat_mul_pi, sin_nat_mul_pi]; ring
  have hpos : 0 < cos (k * π - z) := cos_pos_of_mem_Ioo ⟨by linarith [hw.1, pi_pos], hw.2⟩
  intro h0
  rw [h0, mul_zero] at hc
  linarith

theorem A_eq {k : ℕ} (z : ℝ) : A z = tan (k * π - z) / z := by
  unfold A; rw [tan_eq_neg (k := k) z]; ring

theorem A_pos {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : z ∈ I k) : 0 < A z := by
  rw [A_eq (k := k)]
  have hw := w_mem hz
  exact div_pos (tan_pos_of_pos_of_lt_pi_div_two hw.1 hw.2) (I_pos hk hz)

/-- A は I_k の上で狭義に減る。 -/
theorem A_strictAntiOn {k : ℕ} (hk : 1 ≤ k) : StrictAntiOn A (I k) := by
  intro z₁ h₁ z₂ h₂ h12
  rw [A_eq (k := k) z₁, A_eq (k := k) z₂]
  have hw₁ := w_mem h₁
  have hw₂ := w_mem h₂
  have ht : tan (k * π - z₂) < tan (k * π - z₁) :=
    strictMonoOn_tan ⟨by linarith [hw₂.1, pi_pos], hw₂.2⟩ ⟨by linarith [hw₁.1, pi_pos], hw₁.2⟩
      (by linarith)
  have ht2 : 0 < tan (k * π - z₂) := tan_pos_of_pos_of_lt_pi_div_two hw₂.1 hw₂.2
  have hz₁ := I_pos hk h₁
  rw [div_lt_div_iff₀ (by linarith) hz₁]
  nlinarith

theorem A_eq_iff {z a : ℝ} (hz : z ≠ 0) : A z = a ↔ tan z = -(a * z) := by
  unfold A
  rw [div_eq_iff hz]
  constructor <;> intro h <;> linarith

/-! ### (1) 根の存在と一意 -/

theorem exists_root {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) :
    ∃ z ∈ I k, tan z = -(a * z) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set w₁ := arctan (a * (k * π) + 1) with hw₁
  have hw₁0 : 0 < w₁ := arctan_pos.mpr (by positivity)
  have hw₁1 : w₁ < π / 2 := arctan_lt_pi_div_two _
  let g : ℝ → ℝ := fun w => tan w - a * (k * π - w)
  have hcont : ContinuousOn g (Icc 0 w₁) := by
    apply ContinuousOn.sub
    · exact continuousOn_tan_Ioo.mono (fun w hw => ⟨by linarith [hw.1, pi_pos], by linarith [hw.2]⟩)
    · exact (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
  have hkπ : 0 < a * (k * π) := mul_pos ha (by nlinarith [pi_pos])
  have hg0 : g 0 < 0 := by simp only [g, tan_zero]; linarith
  have hg1 : 0 < g w₁ := by simp only [g, hw₁, tan_arctan]; nlinarith
  obtain ⟨w, hw, hgw⟩ := intermediate_value_Ioo hw₁0.le hcont (show (0 : ℝ) ∈ Ioo (g 0) (g w₁)
    from ⟨hg0, hg1⟩)
  refine ⟨k * π - w, ⟨by linarith [hw.2], by linarith [hw.1]⟩, ?_⟩
  rw [tan_eq_neg (k := k), show k * π - (k * π - w) = w by ring]
  simp only [g] at hgw
  linarith

/-- 第 k の根 z_k(a)（a > 0、k ≥ 1。それ以外では 0 と置く）。 -/
noncomputable def root (k : ℕ) (a : ℝ) : ℝ :=
  if h : 1 ≤ k ∧ 0 < a then Classical.choose (exists_root h.1 h.2) else 0

theorem root_spec {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) :
    root k a ∈ I k ∧ tan (root k a) = -(a * root k a) := by
  unfold root
  split_ifs with h'
  · exact Classical.choose_spec (exists_root h'.1 h'.2)
  · exact absurd ⟨hk, ha⟩ h'

theorem root_A {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a) : A (root k a) = a := by
  obtain ⟨hm, ht⟩ := root_spec hk ha
  exact (A_eq_iff (I_pos hk hm).ne').mpr ht

/-- (1) 根はただ一つ。 -/
theorem root_unique {k : ℕ} (hk : 1 ≤ k) {a z : ℝ} (ha : 0 < a) (hz : z ∈ I k)
    (ht : tan z = -(a * z)) : z = root k a := by
  have h1 : A z = a := (A_eq_iff (I_pos hk hz).ne').mpr ht
  have h2 := root_A hk ha
  exact (A_strictAntiOn hk).injOn hz (root_spec hk ha).1 (h1.trans h2.symm)

theorem root_of_A {k : ℕ} (hk : 1 ≤ k) {z : ℝ} (hz : z ∈ I k) : root k (A z) = z :=
  (root_unique hk (A_pos hk hz) hz ((A_eq_iff (I_pos hk hz).ne').mp rfl)).symm

/-! ### (2) 根は a について減る -/

theorem root_strictAntiOn {k : ℕ} (hk : 1 ≤ k) : StrictAntiOn (root k) (Ioi 0) := by
  intro a ha a' ha' h
  rw [mem_Ioi] at ha ha'
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · have h1 := root_A hk ha
    have h2 := root_A hk ha'
    rw [he] at h1
    linarith
  · have := (A_strictAntiOn hk) (root_spec hk ha).1 (root_spec hk ha').1 hlt
    rw [root_A hk ha, root_A hk ha'] at this; linarith

/-! ### (3) 比は a について増える -/

/-- A の微分の式。 -/
noncomputable def A' (u : ℝ) : ℝ := -(u * (1 + tan u ^ 2) - tan u) / u ^ 2

theorem hasDerivAt_A {u : ℝ} (hc : cos u ≠ 0) (hu : u ≠ 0) : HasDerivAt A (A' u) u := by
  have h := ((hasDerivAt_tan hc).neg).div (hasDerivAt_id' u) hu
  have key : 1 + tan u ^ 2 = 1 / cos u ^ 2 := by
    rw [tan_eq_sin_div_cos, div_pow]
    field_simp
    linarith [sin_sq_add_cos_sq u]
  have e : A = fun u => -tan u / u := rfl
  rw [e]
  convert h using 1
  unfold A'
  rw [key]
  simp only [Pi.neg_apply]
  ring

/-- z·A′(z) = −(1 + A + A²z²)。 -/
theorem mul_A' {u : ℝ} (hu : u ≠ 0) : u * A' u = -(1 + A u + A u ^ 2 * u ^ 2) := by
  unfold A' A
  field_simp
  ring

/-- 交わる点では、A(λt) の傾きは A(t) の傾きより小さい。 -/
theorem slope_gap {t l : ℝ} (ht : 0 < t) (hl : 1 < l) (hA : A (l * t) = A t) (hA0 : A t ≠ 0) :
    l * A' (l * t) < A' t := by
  have e1 := mul_A' (show l * t ≠ 0 by positivity)
  have e2 := mul_A' ht.ne'
  rw [hA] at e1
  have hsq : 0 < A t ^ 2 * t ^ 2 * (l ^ 2 - 1) := by
    apply mul_pos (by positivity) (by nlinarith)
  have : t * (l * A' (l * t)) < t * A' t := by
    rw [show t * (l * A' (l * t)) = l * t * A' (l * t) by ring, e1, e2]
    nlinarith
  exact lt_of_mul_lt_mul_left this ht.le

theorem branch_order {n m : ℕ} (hnm : n < m) {y z : ℝ} (hy : y ∈ I n) (hz : z ∈ I m) : y < z := by
  have h : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
  have : (n : ℝ) * π ≤ (2 * m - 1) * π / 2 := by nlinarith [pi_pos]
  linarith [hy.2, hz.1]

/-- (3) 弱い形：a < a′ なら z_m(a)/z_n(a) ≤ z_m(a′)/z_n(a′)。 -/
theorem ratio_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) {a a' : ℝ} (ha : 0 < a) (haa : a < a') :
    root m a / root n a ≤ root m a' / root n a' := by
  have hm : 1 ≤ m := by omega
  have ha' : 0 < a' := ha.trans haa
  obtain ⟨hY, -⟩ := root_spec hn ha'
  obtain ⟨hy, -⟩ := root_spec hn ha
  obtain ⟨hZ, -⟩ := root_spec hm ha'
  obtain ⟨hz, -⟩ := root_spec hm ha
  set Y := root n a'
  set y := root n a
  set Z := root m a'
  set z := root m a
  have hY0 := I_pos hn hY
  have hy0 := I_pos hn hy
  have hYy : Y < y := root_strictAntiOn hn (mem_Ioi.mpr ha) (mem_Ioi.mpr ha') haa
  set l := Z / Y with hl
  have hl1 : 1 < l := by rw [hl, one_lt_div hY0]; exact branch_order hnm hY hZ
  have hlY : l * Y = Z := by rw [hl]; field_simp
  rw [div_le_iff₀ hy0]
  by_cases hcase : m * π ≤ l * y
  · exact (hz.2.trans_le hcase).le
  push Not at hcase
  have hmem_m : ∀ t ∈ Icc Y y, l * t ∈ I m := by
    intro t ht
    constructor
    · have : Z ≤ l * t := by rw [← hlY]; exact mul_le_mul_of_nonneg_left ht.1 (by linarith)
      linarith [hZ.1]
    · have : l * t ≤ l * y := mul_le_mul_of_nonneg_left ht.2 (by linarith)
      linarith
  have hmem_n : ∀ t ∈ Icc Y y, t ∈ I n := fun t ht => ⟨by linarith [hY.1, ht.1], by
    linarith [hy.2, ht.2]⟩
  have hdf : ∀ t ∈ Icc Y y, HasDerivAt (fun t => A (l * t)) (A' (l * t) * l) t := by
    intro t ht
    have hmt := hmem_m t ht
    exact (hasDerivAt_A (cos_ne_zero_of_mem hmt) (I_pos hm hmt).ne').comp t
      (by simpa using (hasDerivAt_id' t).const_mul l)
  have hdB : ∀ t ∈ Icc Y y, HasDerivAt A (A' t) t := by
    intro t ht
    have hnt := hmem_n t ht
    exact hasDerivAt_A (cos_ne_zero_of_mem hnt) (I_pos hn hnt).ne'
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := Y) (b := y)
    (f := fun t => A (l * t)) (f' := fun t => A' (l * t) * l) (B := A) (B' := A')
    (fun t ht => (hdf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by rw [hlY, root_A hm ha', root_A hn ha'])
    (fun t ht => (hdB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by
      intro t ht heq
      have ht' := Ico_subset_Icc_self ht
      have := slope_gap (I_pos hn (hmem_n t ht')) hl1 heq (A_pos hn (hmem_n t ht')).ne'
      linarith)
    (right_mem_Icc.mpr hYy.le)
  rw [root_A hn ha] at key
  by_contra hlt
  push Not at hlt
  have := (A_strictAntiOn hm) (hmem_m y (right_mem_Icc.mpr hYy.le)) hz hlt
  rw [root_A hm ha] at this
  linarith

/-- (3) z_m/z_n は a について狭義に増える。 -/
theorem ratio_strictMonoOn {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    StrictMonoOn (fun a => root m a / root n a) (Ioi 0) := by
  have hm : 1 ≤ m := by omega
  intro a ha a' ha' haa
  rw [mem_Ioi] at ha ha'
  simp only
  rcases lt_or_eq_of_le (ratio_le hn hnm ha haa) with h | h
  · exact h
  exfalso
  set l := root m a' / root n a' with hl
  have hconst : ∀ b, a ≤ b → b ≤ a' → root m b / root n b = l := by
    intro b hb1 hb2
    have hb : 0 < b := ha.trans_le hb1
    apply le_antisymm
    · rcases eq_or_lt_of_le hb2 with he | hlt
      · rw [he]
      · exact ratio_le hn hnm hb hlt
    · rw [← h]
      rcases eq_or_lt_of_le hb1 with he | hlt
      · rw [he]
      · exact ratio_le hn hnm ha hlt
  obtain ⟨hY, -⟩ := root_spec hn ha'
  obtain ⟨hy, -⟩ := root_spec hn ha
  obtain ⟨hZ, -⟩ := root_spec hm ha'
  set Y := root n a'
  set y := root n a
  have hY0 := I_pos hn hY
  have hYy : Y < y := root_strictAntiOn hn (mem_Ioi.mpr ha) (mem_Ioi.mpr ha') haa
  have hl1 : 1 < l := by rw [hl, one_lt_div hY0]; exact branch_order hnm hY hZ
  -- (Y, y) の上で A(l t) = A(t)
  have hagree : ∀ t ∈ Ioo Y y, A (l * t) = A t ∧ l * t ∈ I m := by
    intro t ht
    have htn : t ∈ I n := ⟨by linarith [hY.1, ht.1], by linarith [hy.2, ht.2]⟩
    set b := A t
    have hb1 : a < b := by
      have := (A_strictAntiOn hn) htn hy ht.2; rw [root_A hn ha] at this; exact this
    have hb2 : b < a' := by
      have := (A_strictAntiOn hn) hY htn ht.1; rw [root_A hn ha'] at this; exact this
    have hb0 : 0 < b := ha.trans hb1
    have hrn : root n b = t := root_of_A hn htn
    have hc := hconst b hb1.le hb2.le
    rw [hrn] at hc
    have hrm : root m b = l * t := by
      rw [div_eq_iff (I_pos hn htn).ne'] at hc; linarith [hc]
    have := root_A hm hb0
    rw [hrm] at this
    have hmem := (root_spec hm hb0).1
    rw [hrm] at hmem
    exact ⟨this, hmem⟩
  set t₀ := (Y + y) / 2
  have ht₀ : t₀ ∈ Ioo Y y := ⟨by simp only [t₀]; linarith, by simp only [t₀]; linarith⟩
  obtain ⟨hA₀, hm₀⟩ := hagree t₀ ht₀
  have htn₀ : t₀ ∈ I n := ⟨by linarith [hY.1, ht₀.1], by linarith [hy.2, ht₀.2]⟩
  have hf : HasDerivAt (fun t => A (l * t)) (A' (l * t₀) * l) t₀ :=
    (hasDerivAt_A (cos_ne_zero_of_mem hm₀) (I_pos hm hm₀).ne').comp t₀
      (by simpa using (hasDerivAt_id' t₀).const_mul l)
  have hB : HasDerivAt A (A' t₀) t₀ :=
    hasDerivAt_A (cos_ne_zero_of_mem htn₀) (I_pos hn htn₀).ne'
  have hev : A =ᶠ[𝓝 t₀] fun t => A (l * t) := by
    filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
    exact (hagree t ht).1.symm
  have hB' : HasDerivAt A (A' (l * t₀) * l) t₀ := hf.congr_of_eventuallyEq hev
  have huniq := hB.unique hB'
  have := slope_gap (I_pos hn htn₀) hl1 hA₀ (A_pos hn htn₀).ne'
  linarith

/-! ### (4) 両端の極限 -/

theorem root_tendsto_zero {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (root k) (𝓝[>] 0) (𝓝 (k * π)) := by
  rw [tendsto_order]
  constructor
  · intro l hl
    set p := max l ((2 * k - 1) * π / 2 + (k * π - (2 * k - 1) * π / 2) / 2)
    have hp : p ∈ I k := by
      constructor
      · have := le_max_right l ((2 * k - 1) * π / 2 + (k * π - (2 * k - 1) * π / 2) / 2)
        have : (0 : ℝ) < k * π - (2 * k - 1) * π / 2 := by nlinarith [pi_pos]
        linarith
      · apply max_lt hl
        have : (0 : ℝ) < k * π - (2 * k - 1) * π / 2 := by nlinarith [pi_pos]
        linarith
    have hAp := A_pos hk hp
    filter_upwards [Ioo_mem_nhdsGT hAp] with a ha
    obtain ⟨hm, -⟩ := root_spec hk ha.1
    have : p < root k a := by
      by_contra hle
      push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · have := root_A hk ha.1; rw [he] at this; linarith [ha.2]
      · have := (A_strictAntiOn hk) hm hp hlt; rw [root_A hk ha.1] at this; linarith [ha.2]
    exact lt_of_le_of_lt (le_max_left _ _) this
  · intro u hu
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (root_spec hk ha).1.2.trans hu

theorem root_tendsto_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (root k) atTop (𝓝 ((2 * k - 1) * π / 2)) := by
  rw [tendsto_order]
  constructor
  · intro l hl
    filter_upwards [eventually_gt_atTop 0] with a ha
    exact hl.trans (root_spec hk ha).1.1
  · intro u hu
    set p := min u ((2 * k - 1) * π / 2 + (k * π - (2 * k - 1) * π / 2) / 2)
    have hgap : (0 : ℝ) < k * π - (2 * k - 1) * π / 2 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [pi_pos]
    have hp : p ∈ I k := by
      constructor
      · apply lt_min hu; linarith
      · have := min_le_right u ((2 * k - 1) * π / 2 + (k * π - (2 * k - 1) * π / 2) / 2)
        linarith
    filter_upwards [eventually_gt_atTop (A p), eventually_gt_atTop 0] with a ha ha0
    obtain ⟨hm, -⟩ := root_spec hk ha0
    have : root k a < p := by
      by_contra hle
      push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · have := root_A hk ha0; rw [← he] at this; linarith
      · have := (A_strictAntiOn hk) hp hm hlt; rw [root_A hk ha0] at this; linarith
    exact lt_of_lt_of_le this (min_le_left _ _)

theorem ratio_tendsto_zero {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun a => root m a / root n a) (𝓝[>] 0) (𝓝 ((m : ℝ) / n)) := by
  have h := (root_tendsto_zero hm).div (root_tendsto_zero hn)
    (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        positivity)
  convert h using 2
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp

theorem ratio_tendsto_atTop {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun a => root m a / root n a) atTop
      (𝓝 ((2 * (m : ℝ) - 1) / (2 * n - 1))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (root_tendsto_atTop hm).div (root_tendsto_atTop hn)
    (by have : (0 : ℝ) < (2 * n - 1) * π / 2 := by nlinarith [pi_pos]
        exact this.ne')
  convert h using 2
  have : (2 * (n : ℝ) - 1) ≠ 0 := by linarith
  field_simp

/-- (4) 第二の共鳴と基音の比 z₂/z₁ は 2 から 3 へ狭義に増える。 -/
theorem second_over_first :
    StrictMonoOn (fun a => root 2 a / root 1 a) (Ioi 0) ∧
    Tendsto (fun a => root 2 a / root 1 a) (𝓝[>] 0) (𝓝 2) ∧
    Tendsto (fun a => root 2 a / root 1 a) atTop (𝓝 3) := by
  refine ⟨ratio_strictMonoOn le_rfl (by norm_num), ?_, ?_⟩
  · have := ratio_tendsto_zero (n := 1) (m := 2) le_rfl (by norm_num)
    norm_num at this
    exact this
  · have := ratio_tendsto_atTop (n := 1) (m := 2) le_rfl (by norm_num)
    norm_num at this
    exact this

end Paper582

end Yamagishi
