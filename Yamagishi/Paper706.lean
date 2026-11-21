/-
論文706『バックテストが測っているのは試した回数である』の格上げ（上からの評価・一般の形）。

原稿（706_yamagishi_a_backtest_measures_the_number_of_attempts/…_jp.tex）は、独立な標準正規の試行
N 本の最良の値の期待値 E[max Zᵢ] を、N = 1・10・100・1000・10000 の数値積分と N = 1000 の乱数で出し、
√(2 ln N) と比べている（最良が 1.0 を超えるのは N = 49 から）。

ここで証明した言明：
  (1) `expect_max_le`：確率空間の上の N ≥ 1 個の実の確率変数 X₁…X_N が、どれも
      E[e^(tXᵢ)] ≤ e^(t²/2)（すべての t）を満たせば、E[max Xᵢ] ≤ √(2 ln N)。
      **独立は要らない**（試行どうしが相関していても、この上界は成り立つ）。
  (2) `expect_max_le_gaussian`：各 Xᵢ が標準正規（平均 0・分散 1）なら (1) の条件が成り立つ
      （Mathlib の `mgf_gaussianReal` から）。よって標準正規の N 本の最大の期待値は √(2 ln N) 以下。
証明の筋：t > 0 で、e^(t·E[max]) ≤ E[e^(t·max)]（e^y ≥ e^a(1 + y − a) を積分する、イェンセンの
不等式の一行版）≤ Σ E[e^(tXᵢ)] ≤ N e^(t²/2)。よって E[max] ≤ (ln N)/t + t/2、t = √(2 ln N) と置く。
形式化していないもの：独立なら N → ∞ で E[max]/√(2 ln N) → 1（下からの評価で、正規分布の裾の評価
が要るため止めた）。N = 49 で最良が 1.0 を超えるという数値。
注意（下読みの AI の指摘）：原稿は「増え方は対数でしかない」と書くが、上界は対数の平方根
√(2 ln N) で、対数よりさらに遅い。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper706

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option linter.unusedSectionVars false

/-- 最大の値。 -/
noncomputable def maxX {n : ℕ} (X : Fin (n + 1) → Ω → ℝ) : Ω → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty X

theorem maxX_apply {n : ℕ} (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) :
    maxX X ω = Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) := by
  unfold maxX; rw [Finset.sup'_apply]

/-- (1) E[e^(tXᵢ)] ≤ e^(t²/2) なら E[max] ≤ √(2 ln N)（独立は要らない）。 -/
theorem expect_max_le {n : ℕ} (X : Fin (n + 1) → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) P)
    (hexp : ∀ i (t : ℝ), Integrable (fun ω => exp (t * X i ω)) P)
    (hmgf : ∀ i (t : ℝ), ∫ ω, exp (t * X i ω) ∂P ≤ exp (t ^ 2 / 2)) :
    ∫ ω, maxX X ω ∂P ≤ √(2 * log (n + 1)) := by
  have hMmeas : Measurable (maxX X) :=
    Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hmeas i)
  -- 最大はどれかの Xⱼ に等しい
  have hattain : ∀ ω, ∃ j, maxX X ω = X j ω := by
    intro ω
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
    exact ⟨j, by rw [maxX_apply, hj]⟩
  have hMint : Integrable (maxX X) P := by
    refine Integrable.mono'
      (integrable_finsetSum Finset.univ (f := fun i ω => |X i ω|) (fun i _ => (hint i).abs))
      hMmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    obtain ⟨j, hj⟩ := hattain ω
    rw [Real.norm_eq_abs, hj]
    exact Finset.single_le_sum (f := fun i => |X i ω|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
  -- t > 0 での評価 t·E[max] ≤ ln N + t²/2
  have key : ∀ t : ℝ, 0 < t → t * ∫ ω, maxX X ω ∂P ≤ log (n + 1) + t ^ 2 / 2 := by
    intro t ht
    set E := ∫ ω, maxX X ω ∂P
    have hbound : ∀ ω, exp (t * maxX X ω) ≤ ∑ i, exp (t * X i ω) := by
      intro ω
      obtain ⟨j, hj⟩ := hattain ω
      rw [hj]
      exact Finset.single_le_sum (f := fun i => exp (t * X i ω)) (fun i _ => (exp_pos _).le)
        (Finset.mem_univ j)
    have hsumint : Integrable (fun ω => ∑ i, exp (t * X i ω)) P :=
      integrable_finsetSum Finset.univ (f := fun i ω => exp (t * X i ω)) (fun i _ => hexp i t)
    have hexpM : Integrable (fun ω => exp (t * maxX X ω)) P := by
      refine Integrable.mono' hsumint
        ((hMmeas.const_mul t).exp.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact hbound ω
    -- イェンセン（接線の一行版）：e^(tE) ≤ E[e^(t·max)]
    have hjensen : exp (t * E) ≤ ∫ ω, exp (t * maxX X ω) ∂P := by
      set a := t * E
      have hpt : ∀ ω, exp a * (1 + (t * maxX X ω - a)) ≤ exp (t * maxX X ω) := by
        intro ω
        have := Real.add_one_le_exp (t * maxX X ω - a)
        have h2 : exp (t * maxX X ω) = exp a * exp (t * maxX X ω - a) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]
        exact mul_le_mul_of_nonneg_left (by linarith) (exp_pos a).le
      have hlin : ∫ ω, exp a * (1 + (t * maxX X ω - a)) ∂P = exp a := by
        have : (fun ω => exp a * (1 + (t * maxX X ω - a))) =
            fun ω => exp a * (1 - a) + (exp a * t) * maxX X ω := by
          funext ω; ring
        rw [this, integral_add (integrable_const _) (hMint.const_mul _), integral_const,
          integral_const_mul]
        simp only [probReal_univ, one_smul]
        simp only [a, E]; ring
      calc exp a = ∫ ω, exp a * (1 + (t * maxX X ω - a)) ∂P := hlin.symm
        _ ≤ ∫ ω, exp (t * maxX X ω) ∂P := by
          apply integral_mono _ hexpM hpt
          exact (integrable_const _).add ((hMint.const_mul t).sub (integrable_const _))
            |>.const_mul _
    have hsum : ∫ ω, exp (t * maxX X ω) ∂P ≤ (n + 1) * exp (t ^ 2 / 2) := by
      calc ∫ ω, exp (t * maxX X ω) ∂P ≤ ∫ ω, ∑ i, exp (t * X i ω) ∂P :=
            integral_mono hexpM hsumint hbound
        _ = ∑ i, ∫ ω, exp (t * X i ω) ∂P := integral_finsetSum _ (fun i _ => hexp i t)
        _ ≤ ∑ _i : Fin (n + 1), exp (t ^ 2 / 2) := Finset.sum_le_sum (fun i _ => hmgf i t)
        _ = (n + 1) * exp (t ^ 2 / 2) := by simp
    have h3 : exp (t * E) ≤ (n + 1) * exp (t ^ 2 / 2) := hjensen.trans hsum
    have hN : (0 : ℝ) < n + 1 := by positivity
    have h4 := Real.log_le_log (exp_pos _) h3
    rw [Real.log_exp, Real.log_mul hN.ne' (exp_pos _).ne', Real.log_exp] at h4
    exact h4
  set E := ∫ ω, maxX X ω ∂P
  set L := log ((n : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · -- N = 1：E ≤ t/2 がすべての t > 0 で成り立つので E ≤ 0
    rw [← hL0, mul_zero, Real.sqrt_zero]
    by_contra hE
    push Not at hE
    have := key E hE
    rw [← hL0] at this
    nlinarith
  · set t := √(2 * L)
    have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have ht2 : t ^ 2 = 2 * L := Real.sq_sqrt (by linarith)
    have := key t ht
    have : t * E ≤ t * t := by nlinarith
    exact le_of_mul_le_mul_left this ht

/-- (2) 標準正規なら条件が成り立つ：E[max] ≤ √(2 ln N)（独立は要らない）。 -/
theorem expect_max_le_gaussian {n : ℕ} (X : Fin (n + 1) → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    ∫ ω, maxX X ω ∂P ≤ √(2 * log (n + 1)) := by
  apply expect_max_le X hmeas
  · intro i
    exact (hlaw i).integrable ((memLp_id_gaussianReal 1).integrable le_rfl)
  · intro i t
    exact (hlaw i).integrable_comp (f := fun x => exp (t * x))
      (integrable_exp_mul_gaussianReal t)
  · intro i t
    have := mgf_gaussianReal (hlaw i) t
    simp only [mgf, zero_mul, zero_add, NNReal.coe_one, one_mul] at this
    rw [this]

end Paper706

end Yamagishi
