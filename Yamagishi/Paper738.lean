/-
論文738『シャープレシオを二百五十二の平方根倍して年率にしてよいのは、日々の収益が無関係なときだけ』の格上げ（一般の形）。

原稿（738_yamagishi_annualising_a_sharpe_ratio_assumes_no_memory/…_jp.tex）は、
年間の和の分散 σ²(q + 2Σ_{k=1}^{q−1}(q − k)ρ^k) から比 R_q = √(q/(q + 2Σ(q − k)ρ^k)) を立て、
ρ = ±0.1, ±0.3, 0.5 と q = 252 の値、ρ = +0.3 での q = 4, 12, 52, 252 の値で、
「正の自己相関で過大、負で過小」「細かい周期から直すほど外れが大きい」と述べる。

ここで証明した言明（−1 < ρ < 1、q は自然数）：
  (0) `S_closed`：(1 − ρ)²·Σ_{k=1}^{q−1}(q − k)ρ^k = ρ(q(1 − ρ) − (1 − ρ^q))。
  (1) `R_lt_one_iff`・`R_gt_one_iff`：q ≥ 2 で R_q < 1 ⇔ ρ > 0、R_q > 1 ⇔ ρ < 0。
      （年間の分散が正であること `var_pos` も示した。）
  (2) `R_tendsto`：q → ∞ で R_q → √((1 − ρ)/(1 + ρ))。
  (3) `h_antitone_iff`：h(q) = (1 − ρ^q)/q が q ≥ 1 で単調に減る ⇔ ρ ≥ −1/2
      （q = 2 での条件が 1 − 3ρ² + 2ρ³ = (1 − ρ)²(1 + 2ρ) ≥ 0）。
      `R_antitone_of_pos`：0 ≤ ρ なら R_q は q について減る（1 より下へ離れていく）。
      `R_monotone_of_neg`：−1/2 ≤ ρ ≤ 0 なら R_q は q について増える（1 より上へ離れていく）。
      `R_zigzag`：ρ < −1/2 なら R_3 < R_2（R_2 > 1 なのに戻る。単調に離れない）。
足した仮定：比は原稿の分散の式（AR(1) 型の自己相関 ρ^k、一年を何期に割っても同じ ρ）を定義として置いた。
確かめの係の案との違い：係は (3) を「外れが単調になるのは ρ ≥ −1/2 のときだけ」と書いた。機械で確かめた
のは、比の分散の部分 g(q) = (1+ρ)/(1−ρ) − (2ρ/(1−ρ)²)h(q) を通して、h の単調性 ⇔ ρ ≥ −1/2 と、
そこから R_q の単調性が出ること、ρ < −1/2 では q = 2 → 3 で戻ることである（係の案のとおり）。
形式化していないもの：乱数 8000 年の値、日次 SR から年率 SR への数値、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper738

open Real Finset Filter Topology

/-- Σ_{k=1}^{q−1} (q − k) ρ^k。 -/
noncomputable def S (q : ℕ) (ρ : ℝ) : ℝ := ∑ k ∈ Ico 1 q, ((q : ℝ) - k) * ρ ^ k

/-- 年間の分散 ÷ (qσ²)。 -/
noncomputable def g (q : ℕ) (ρ : ℝ) : ℝ := ((q : ℝ) + 2 * S q ρ) / q

/-- 正しい年率 ÷ √q 倍の比 R_q = √(q/(q + 2S))。 -/
noncomputable def R (q : ℕ) (ρ : ℝ) : ℝ := √((q : ℝ) / ((q : ℝ) + 2 * S q ρ))

theorem geom_Ico (ρ : ℝ) {q : ℕ} (hq : 1 ≤ q) : (1 - ρ) * ∑ k ∈ Ico 1 q, ρ ^ k = ρ - ρ ^ q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn, mul_add, ih, pow_succ]; ring

theorem S_succ (ρ : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    S (q + 1) ρ = S q ρ + ∑ k ∈ Ico 1 q, ρ ^ k + ρ ^ q := by
  unfold S
  rw [sum_Ico_succ_top hq]
  push_cast
  have : ∑ k ∈ Ico 1 q, ((q : ℝ) + 1 - k) * ρ ^ k =
      ∑ k ∈ Ico 1 q, ((q : ℝ) - k) * ρ ^ k + ∑ k ∈ Ico 1 q, ρ ^ k := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro k _; ring
  rw [this]; ring

/-- (0) 和の閉じた形。 -/
theorem S_closed (ρ : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    (1 - ρ) ^ 2 * S q ρ = ρ * (q * (1 - ρ) - (1 - ρ ^ q)) := by
  induction q, hq using Nat.le_induction with
  | base => simp [S]
  | succ n hn ih =>
    rw [S_succ ρ hn]
    have hg := geom_Ico ρ hn
    push_cast
    have : (1 - ρ) ^ 2 * (S n ρ + ∑ k ∈ Ico 1 n, ρ ^ k + ρ ^ n) =
        (1 - ρ) ^ 2 * S n ρ + (1 - ρ) * ((1 - ρ) * ∑ k ∈ Ico 1 n, ρ ^ k) +
            (1 - ρ) ^ 2 * ρ ^ n := by ring
    rw [this, ih, hg, pow_succ]; ring

/-- Σ_{j<q} ρ^j < q（q ≥ 2、|ρ| < 1）。 -/
theorem geom_lt (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    ∑ j ∈ range q, ρ ^ j < q := by
  have hab : |ρ| ≤ 1 := abs_le.mpr ⟨h1.le, h2.le⟩
  have : ∑ j ∈ range q, ρ ^ j < ∑ j ∈ range q, (1 : ℝ) := by
    apply sum_lt_sum
    · intro j _
      calc ρ ^ j ≤ |ρ ^ j| := le_abs_self _
        _ = |ρ| ^ j := abs_pow ρ j
        _ ≤ 1 := pow_le_one₀ (abs_nonneg ρ) hab
    · exact ⟨1, mem_range.mpr (by omega), by simpa using h2⟩
  simpa using this

/-- 括弧 B = q(1 − ρ) − (1 − ρ^q) は q ≥ 2 で正。 -/
theorem bracket_pos (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    0 < q * (1 - ρ) - (1 - ρ ^ q) := by
  have hgs := geom_sum_mul ρ q
  have hlt := geom_lt ρ h1 h2 hq
  have : q * (1 - ρ) - (1 - ρ ^ q) = (1 - ρ) * (q - ∑ j ∈ range q, ρ ^ j) := by
    have : (1 - ρ ^ q) = (∑ j ∈ range q, ρ ^ j) * (1 - ρ) := by linarith
    rw [this]; ring
  rw [this]
  exact mul_pos (by linarith) (by linarith)

theorem S_pos_iff (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    0 < S q ρ ↔ 0 < ρ := by
  have hc := S_closed ρ (by omega : 1 ≤ q)
  have hB := bracket_pos ρ h1 h2 hq
  have h1r : 0 < (1 - ρ) ^ 2 := by have : 0 < 1 - ρ := by linarith
                                   positivity
  constructor
  · intro hS
    by_contra hr; push Not at hr
    have : ρ * (q * (1 - ρ) - (1 - ρ ^ q)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr hB.le
    nlinarith
  · intro hr
    have : 0 < ρ * (q * (1 - ρ) - (1 - ρ ^ q)) := mul_pos hr hB
    rw [← hc] at this
    exact pos_of_mul_pos_right this h1r.le

theorem S_neg_iff (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    S q ρ < 0 ↔ ρ < 0 := by
  have hc := S_closed ρ (by omega : 1 ≤ q)
  have hB := bracket_pos ρ h1 h2 hq
  have h1r : 0 < (1 - ρ) ^ 2 := by have : 0 < 1 - ρ := by linarith
                                   positivity
  constructor
  · intro hS
    by_contra hr; push Not at hr
    have : 0 ≤ ρ * (q * (1 - ρ) - (1 - ρ ^ q)) := mul_nonneg hr hB.le
    nlinarith
  · intro hr
    have : ρ * (q * (1 - ρ) - (1 - ρ ^ q)) < 0 := mul_neg_of_neg_of_pos hr hB
    rw [← hc] at this
    by_contra hS; push Not at hS
    nlinarith

/-- 年間の分散は正：q + 2S > 0（q ≥ 1）。 -/
theorem var_pos (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 1 ≤ q) :
    0 < (q : ℝ) + 2 * S q ρ := by
  have hc := S_closed ρ hq
  have h1r : 0 < (1 - ρ) ^ 2 := by have : 0 < 1 - ρ := by linarith
                                   positivity
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : ρ ^ q < 1 := by
    have : |ρ ^ q| < 1 := by
      rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg ρ) (abs_lt.mpr ⟨h1, h2⟩) (by omega)
    exact (abs_lt.mp this).2
  -- (1 − ρ)²(q + 2S) = q(1 − ρ²) − 2ρ(1 − ρ^q)
  have key : (1 - ρ) ^ 2 * ((q : ℝ) + 2 * S q ρ) = q * (1 - ρ ^ 2) - 2 * ρ * (1 - ρ ^ q) := by
    rw [mul_add, mul_left_comm, hc]; ring
  have hpos : 0 < q * (1 - ρ ^ 2) - 2 * ρ * (1 - ρ ^ q) := by
    rcases le_or_gt ρ 0 with hr | hr
    · have : 0 < (q : ℝ) * (1 - ρ ^ 2) := by
        apply mul_pos (by linarith); nlinarith
      nlinarith
    · -- ρ > 0：(1 − ρ)²(q + 2S) ≥ (1 − ρ)² q
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · have : q = 1 := by omega
        subst this; simp; nlinarith
      · have hS := (S_pos_iff ρ h1 h2 hq2).mpr hr
        rw [← key]; positivity
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos h1r.le

/-- (1) q ≥ 2 で R_q < 1 ⇔ ρ > 0。 -/
theorem R_lt_one_iff (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    R q ρ < 1 ↔ 0 < ρ := by
  have hv := var_pos ρ h1 h2 (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [R, sqrt_lt' one_pos, one_pow, div_lt_one hv, ← S_pos_iff ρ h1 h2 hq]
  constructor <;> intro h <;> linarith

/-- (1) q ≥ 2 で R_q > 1 ⇔ ρ < 0。 -/
theorem R_gt_one_iff (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 2 ≤ q) :
    1 < R q ρ ↔ ρ < 0 := by
  have hv := var_pos ρ h1 h2 (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [R, lt_sqrt zero_le_one, one_pow, one_lt_div hv, ← S_neg_iff ρ h1 h2 hq]
  constructor <;> intro h <;> linarith

/-- g(q) = (1+ρ)/(1−ρ) − (2ρ/(1−ρ)²)·(1 − ρ^q)/q（q ≥ 1）。 -/
theorem g_eq (ρ : ℝ) (h2 : ρ < 1) {q : ℕ} (hq : 1 ≤ q) :
    g q ρ = (1 + ρ) / (1 - ρ) - 2 * ρ / (1 - ρ) ^ 2 * ((1 - ρ ^ q) / q) := by
  have hc := S_closed ρ hq
  have h1r : (1 - ρ) ≠ 0 := by linarith
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hS : S q ρ = ρ * (q * (1 - ρ) - (1 - ρ ^ q)) / (1 - ρ) ^ 2 := by
    rw [← hc]; field_simp
  unfold g
  rw [hS]
  field_simp
  ring

/-- (2) q → ∞ で R_q → √((1 − ρ)/(1 + ρ))。 -/
theorem R_tendsto (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) :
    Tendsto (fun q : ℕ => R q ρ) atTop (𝓝 (√((1 - ρ) / (1 + ρ)))) := by
  have hp : Tendsto (fun q : ℕ => ρ ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.mpr ⟨h1, h2⟩)
  have hinv : Tendsto (fun q : ℕ => (1 : ℝ) / q) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Tendsto (fun q : ℕ =>
      (1 + ρ) / (1 - ρ) - 2 * ρ / (1 - ρ) ^ 2 * ((1 - ρ ^ q) * (1 / q)))
      atTop (𝓝 ((1 + ρ) / (1 - ρ) - 2 * ρ / (1 - ρ) ^ 2 * ((1 - 0) * 0))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hp).mul hinv))
  simp only [sub_zero, mul_zero] at hlim
  have hg : Tendsto (fun q : ℕ => g q ρ) atTop (𝓝 ((1 + ρ) / (1 - ρ))) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with q hq
    rw [g_eq ρ h2 hq]; ring
  have hne : (1 + ρ) / (1 - ρ) ≠ 0 := by
    apply div_ne_zero <;> linarith
  have hR : ∀ q : ℕ, 1 ≤ q → R q ρ = √((g q ρ)⁻¹) := by
    intro q hq; unfold R g; rw [inv_div]
  have := (hg.inv₀ hne).sqrt
  rw [inv_div] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [hR q hq]

/-- h(q) = (1 − ρ^q)/q。 -/
noncomputable def h (q : ℕ) (ρ : ℝ) : ℝ := (1 - ρ ^ q) / q

/-- q(q + 1)(h(q) − h(q + 1)) = 1 − (q + 1)ρ^q + qρ^(q+1)。 -/
theorem h_diff (ρ : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    h q ρ - h (q + 1) ρ = (1 - (q + 1) * ρ ^ q + q * ρ ^ (q + 1)) / (q * (q + 1)) := by
  unfold h
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem three_q_le (q : ℕ) (hq : 2 ≤ q) : (3 * q + 2 : ℝ) ≤ 2 ^ (q + 1) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at *; rw [pow_succ]; linarith

/-- (3) h(q) が q ≥ 1 で単調に減る ⇔ ρ ≥ −1/2（−1 < ρ < 1）。 -/
theorem h_antitone_iff (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) :
    (∀ q : ℕ, 1 ≤ q → h (q + 1) ρ ≤ h q ρ) ↔ -1 / 2 ≤ ρ := by
  constructor
  · intro H
    by_contra hr; push Not at hr
    have := H 2 (by norm_num)
    have hd := h_diff ρ (q := 2) (by norm_num)
    have : 0 ≤ h 2 ρ - h (2 + 1) ρ := by linarith
    rw [hd] at this
    have hnum : (1 - ((2 : ℕ) + 1) * ρ ^ 2 + (2 : ℕ) * ρ ^ (2 + 1) : ℝ) =
        (1 - ρ) ^ 2 * (1 + 2 * ρ) := by
      push_cast; ring
    rw [hnum] at this
    have : (1 - ρ) ^ 2 * (1 + 2 * ρ) < 0 := by
      apply mul_neg_of_pos_of_neg (by nlinarith) (by linarith)
    have hden : (0 : ℝ) < ((2 : ℕ) : ℝ) * ((2 : ℕ) + 1) := by norm_num
    have := div_neg_of_neg_of_pos this hden
    linarith
  · intro hr q hq
    have hd := h_diff ρ hq
    have hden : (0 : ℝ) < q * (q + 1) := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    suffices hD : 0 ≤ 1 - (q + 1) * ρ ^ q + q * ρ ^ (q + 1) by
      have : 0 ≤ h q ρ - h (q + 1) ρ := by rw [hd]; exact div_nonneg hD hden.le
      linarith
    rcases le_or_gt 0 ρ with h0 | h0
    · -- 0 ≤ ρ < 1：D = (1 − ρ)Σ_{j<q}(ρ^j − ρ^q) ≥ 0
      have hgs := geom_sum_mul ρ q
      have hsum : (q : ℝ) * ρ ^ q ≤ ∑ j ∈ range q, ρ ^ j := by
        have : ∑ j ∈ range q, ρ ^ q ≤ ∑ j ∈ range q, ρ ^ j := by
          apply sum_le_sum; intro j hj
          exact pow_le_pow_of_le_one h0 h2.le (by simp at hj; omega)
        simpa using this
      have : 1 - (q + 1) * ρ ^ q + q * ρ ^ (q + 1) =
          (1 - ρ) * (∑ j ∈ range q, ρ ^ j - q * ρ ^ q) := by
        rw [pow_succ]
        have : (1 - ρ ^ q) = (∑ j ∈ range q, ρ ^ j) * (1 - ρ) := by linarith
        linear_combination this
      rw [this]
      exact mul_nonneg (by linarith) (by linarith)
    · -- ρ = −a、0 < a ≤ 1/2
      set a := -ρ with ha
      have ha0 : 0 < a := by linarith
      have ha2 : a ≤ 1 / 2 := by linarith
      have hρ : ρ = -a := by linarith
      rw [hρ]
      rcases Nat.even_or_odd q with he | ho
      · rw [he.neg_pow, (he.add_one).neg_pow]
        -- (q + 1)a^q + q a^(q+1) ≤ (3q + 2)/2^(q+1) ≤ 1
        obtain ⟨m, hm⟩ := he
        have hq2 : 2 ≤ q := by omega
        have hap : a ^ q ≤ (1 / 2) ^ q := pow_le_pow_left₀ ha0.le ha2 q
        have hap1 : a ^ (q + 1) ≤ (1 / 2) ^ (q + 1) := pow_le_pow_left₀ ha0.le ha2 (q + 1)
        have h3 := three_q_le q hq2
        have hq0 : (0 : ℝ) ≤ q := by positivity
        have e : (q + 1 : ℝ) * (1 / 2) ^ q + q * (1 / 2) ^ (q + 1) = (3 * q + 2) / 2 ^ (q + 1) := by
          rw [one_div_pow, one_div_pow, pow_succ]; field_simp; ring
        have : (3 * q + 2 : ℝ) / 2 ^ (q + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact h3
        have : (q + 1 : ℝ) * a ^ q + q * a ^ (q + 1) ≤ 1 := by
          calc (q + 1 : ℝ) * a ^ q + q * a ^ (q + 1)
              ≤ (q + 1 : ℝ) * (1 / 2) ^ q + q * (1 / 2) ^ (q + 1) := by
                gcongr
            _ ≤ 1 := by rwa [e]
        linarith
      · rw [ho.neg_pow, (ho.add_one).neg_pow]
        have : 0 ≤ (q + 1 : ℝ) * a ^ q + q * a ^ (q + 1) := by positivity
        linarith

/-- R_q = 1/√g(q)。R は g について減る。 -/
theorem R_eq (ρ : ℝ) (q : ℕ) : R q ρ = √((g q ρ)⁻¹) := by
  unfold R g; rw [inv_div]

theorem g_pos (ρ : ℝ) (h1 : -1 < ρ) (h2 : ρ < 1) {q : ℕ} (hq : 1 ≤ q) : 0 < g q ρ := by
  unfold g
  exact div_pos (var_pos ρ h1 h2 hq) (by exact_mod_cast (by omega : 0 < q))

/-- (3) 0 ≤ ρ < 1：R_q は q について減る。 -/
theorem R_antitone_of_pos (ρ : ℝ) (h0 : 0 ≤ ρ) (h2 : ρ < 1) {q : ℕ} (hq : 1 ≤ q) :
    R (q + 1) ρ ≤ R q ρ := by
  have h1 : -1 < ρ := by linarith
  have hh := (h_antitone_iff ρ h1 h2).mpr (by linarith) q hq
  rw [R_eq, R_eq]
  apply sqrt_le_sqrt
  apply inv_anti₀ (g_pos ρ h1 h2 hq)
  rw [g_eq ρ h2 hq, g_eq ρ h2 (by omega)]
  have : 0 ≤ 2 * ρ / (1 - ρ) ^ 2 := by
    apply div_nonneg (by linarith); positivity
  unfold h at hh
  push_cast at hh ⊢
  nlinarith

/-- (3) −1/2 ≤ ρ ≤ 0：R_q は q について増える。 -/
theorem R_monotone_of_neg (ρ : ℝ) (h0 : ρ ≤ 0) (hr : -1 / 2 ≤ ρ) {q : ℕ} (hq : 1 ≤ q) :
    R q ρ ≤ R (q + 1) ρ := by
  have h1 : -1 < ρ := by linarith
  have h2 : ρ < 1 := by linarith
  have hh := (h_antitone_iff ρ h1 h2).mpr hr q hq
  rw [R_eq, R_eq]
  apply sqrt_le_sqrt
  apply inv_anti₀ (g_pos ρ h1 h2 (by omega))
  rw [g_eq ρ h2 hq, g_eq ρ h2 (by omega)]
  have : 2 * ρ / (1 - ρ) ^ 2 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by linarith); positivity
  unfold h at hh
  push_cast at hh ⊢
  nlinarith

/-- (3) ρ < −1/2：R_3 < R_2（q = 2 から 3 で 1 の側へ戻る）。 -/
theorem R_zigzag (ρ : ℝ) (h1 : -1 < ρ) (hr : ρ < -1 / 2) : R 3 ρ < R 2 ρ := by
  have h2 : ρ < 1 := by linarith
  rw [R_eq, R_eq]
  apply sqrt_lt_sqrt (inv_nonneg.mpr (g_pos ρ h1 h2 (by norm_num)).le)
  apply inv_strictAnti₀ (g_pos ρ h1 h2 (by norm_num))
  rw [g_eq ρ h2 (q := 2) (by norm_num), g_eq ρ h2 (q := 3) (by norm_num)]
  have hc : 2 * ρ / (1 - ρ) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos (by linarith); nlinarith
  -- h(3) − h(2) = −(1 − ρ)²(1 + 2ρ)/6 > 0
  have : (1 - ρ ^ 2) / ((2 : ℕ) : ℝ) < (1 - ρ ^ 3) / ((3 : ℕ) : ℝ) := by
    push_cast
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [sq_nonneg (1 - ρ), mul_pos (sq_pos_of_pos (by linarith : (0:ℝ) < 1 - ρ))
      (by linarith : (0:ℝ) < -(1 + 2 * ρ))]
  nlinarith

end Paper738

end Yamagishi
