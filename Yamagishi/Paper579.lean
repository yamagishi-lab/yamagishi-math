/-
論文579『正答率は問題の性質ではなく、問題と集団の関係である』の芯（格上げの一部）。

原稿（579_yamagishi_the_rate_belongs_to_question_and_group/…_jp.tex）は、二母数ロジスティック
P(θ) = 1/(1 + e^(−a(θ−b))) と、平均 μ・標準偏差 1 の正規分布の集団の正答率 p(μ) = ∫P(θ)φ(θ − μ)dθ で、
識別力 2.0 と 0.5 の二問の正答率が平均 0.327653 で一度だけ入れ替わることを数値で示し、識別力が
等しければ入れ替わらないことを一文の言葉で述べる。

ここで証明した言明（芯だけ）：
  (1) `individual_sign`・`individual_single_crossing`：個人の段では、識別力 a_A ≠ a_B（正）なら
      P_A(θ) − P_B(θ) の符号は一次式 (a_A − a_B)θ − (a_A b_A − a_B b_B) の符号と同じで、
      二つの曲線はちょうど一点 θ* = (a_A b_A − a_B b_B)/(a_A − a_B) で交わる。
  (2) `equal_discrimination_order`：識別力が等しい（a_A = a_B = a > 0）なら、困難度 b_A ≤ b_B のとき
      どんな能力の分布（任意の確率測度）の集団でも p_A ≥ p_B。
      `equal_discrimination_strict`：b_A < b_B なら p_A > p_B（狭義）。
      したがって、識別力が等しい二問の正答率の順は、どの集団でも入れ替わらない。
形式化していないもの（重い所）：集団の段で「正規分布（対数凹の密度）の集団では交わりがちょうど一回」
（カーリンの変動減少性。Mathlib に全正値性の道具がまだ無い）、二峰の集団で三回交わる例
（確かめの係の数値）、θ* = 4/15 と 0.327653 の値、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper579

open Real MeasureTheory

/-- 二母数ロジスティック P(θ) = 1/(1 + e^(−a(θ−b)))。 -/
noncomputable def P (a b θ : ℝ) : ℝ := 1 / (1 + exp (-(a * (θ - b))))

/-- ロジスティック関数 σ(z) = 1/(1 + e^(−z)) は狭義に増える。 -/
theorem sigma_strictMono : StrictMono (fun z : ℝ => 1 / (1 + exp (-z))) := by
  intro x y h
  simp only
  apply one_div_lt_one_div_of_lt (by positivity)
  have : exp (-y) < exp (-x) := exp_lt_exp.mpr (by linarith)
  linarith

theorem P_lt_iff (a b a' b' θ : ℝ) : P a b θ < P a' b' θ ↔ a * (θ - b) < a' * (θ - b') :=
  sigma_strictMono.lt_iff_lt

/-- (1) 差の符号は一次式の符号。 -/
theorem individual_sign (aA bA aB bB θ : ℝ) :
    (P aB bB θ < P aA bA θ ↔ 0 < (aA - aB) * θ - (aA * bA - aB * bB)) ∧
    (P aA bA θ = P aB bB θ ↔ (aA - aB) * θ - (aA * bA - aB * bB) = 0) := by
  constructor
  · rw [P_lt_iff]; constructor <;> intro h <;> linarith
  · constructor
    · intro h
      have := sigma_strictMono.injective h
      linarith
    · intro h
      unfold P
      congr 3
      linarith

/-- (1) 識別力が違えば、曲線はちょうど一点 θ* で交わる。 -/
theorem individual_single_crossing {aA bA aB bB : ℝ} (hne : aA ≠ aB) :
    ∃! θ, P aA bA θ = P aB bB θ := by
  have hd : aA - aB ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨(aA * bA - aB * bB) / (aA - aB), ?_, ?_⟩
  · show P aA bA _ = P aB bB _
    rw [(individual_sign aA bA aB bB _).2]; field_simp; ring
  · intro θ h
    rw [(individual_sign aA bA aB bB _).2] at h
    field_simp; linarith

theorem P_cont (a b : ℝ) : Continuous (P a b) := by
  have h : Continuous fun θ : ℝ => 1 + exp (-(a * (θ - b))) := by fun_prop
  exact continuous_const.div h (fun θ => ne_of_gt (add_pos one_pos (exp_pos _)))

theorem P_bdd (a b θ : ℝ) : |P a b θ| ≤ 1 := by
  unfold P
  rw [abs_of_pos (by positivity), div_le_one (by positivity)]
  linarith [exp_pos (-(a * (θ - b)))]

theorem P_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ) : Integrable (P a b) μ := by
  refine Integrable.of_bound (P_cont a b).aestronglyMeasurable 1 ?_
  exact Filter.Eventually.of_forall (fun θ => by rw [Real.norm_eq_abs]; exact P_bdd a b θ)

/-- (2) 識別力が等しく b_A ≤ b_B なら、どんな集団でも p_A ≥ p_B。 -/
theorem equal_discrimination_order (μ : Measure ℝ) [IsProbabilityMeasure μ] {a bA bB : ℝ}
    (ha : 0 < a) (hb : bA ≤ bB) :
    ∫ θ, P a bB θ ∂μ ≤ ∫ θ, P a bA θ ∂μ := by
  apply integral_mono (P_integrable μ a bB) (P_integrable μ a bA)
  intro θ
  rcases eq_or_lt_of_le hb with h | h
  · rw [h]
  · exact le_of_lt ((P_lt_iff a bB a bA θ).mpr (by nlinarith))

/-- (2) b_A < b_B なら狭義に p_A > p_B。 -/
theorem equal_discrimination_strict (μ : Measure ℝ) [IsProbabilityMeasure μ] {a bA bB : ℝ}
    (ha : 0 < a) (hb : bA < bB) :
    ∫ θ, P a bB θ ∂μ < ∫ θ, P a bA θ ∂μ := by
  have hpt : ∀ θ, P a bB θ < P a bA θ := fun θ => (P_lt_iff a bB a bA θ).mpr (by nlinarith)
  rw [← sub_pos, ← integral_sub (P_integrable μ a bA) (P_integrable μ a bB)]
  have hpos : ∀ θ, 0 < P a bA θ - P a bB θ := fun θ => sub_pos.mpr (hpt θ)
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hpos θ).le)
    ((P_integrable μ a bA).sub (P_integrable μ a bB))]
  have : Function.support (fun θ => P a bA θ - P a bB θ) = Set.univ := by
    ext θ; simp only [Function.mem_support, Set.mem_univ, iff_true]; exact ne_of_gt (hpos θ)
  rw [this]; simp

end Paper579

end Yamagishi
