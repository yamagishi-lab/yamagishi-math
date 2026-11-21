/-
論文935『上下法が追う割合は下げる規則が選び、非対称な規則では集まる点が歩幅に比例して上にずれる』の芯（格上げの一部）。

原稿（935_yamagishi_the_rule_of_an_up_down_method_chooses_the_proportion_it_tracks/…_jp.tex）は、
k 回続けて正しければ歩幅だけ下げ、一度でも誤れば上げる規則で、釣り合いの点 P(x*)^k = 1/2 を
既知として書き、集まる点のずれを乱数の観察者（k = 1〜3、歩幅 0.1・0.5・1.0）の実測で並べる。
射程注記に「ずれの係数を理論にしない」とある。

ここで証明した言明（芯だけ）：
  (1) `step_probs`：一歩の向きを決めるまでの試行で、下がる確率は P^k、上がる確率は 1 − P^k
      （k 回続けて正しい確率と、それより前に一度誤る確率 Σ_{m<k} P^m(1 − P) の和が 1）。
  (2) `expected_trials`：一歩にかかる試行の数の期待値は Σ_{m=1}^{k} m P^(m−1)(1 − P)（途中で誤る）
      + k P^k（k 回正しい）= 1 + P + … + P^(k−1)。
  (3) `detailed_balance_stationary`：格子の上の出生死滅の鎖（上がる確率 u_j、下がる確率 d_j、
      とどまる確率 1 − u_j − d_j）で、詳細釣り合い π_{j+1} d_{j+1} = π_j u_j を満たす π は、
      各点の釣り合いの式 π_{j−1}u_{j−1} + π_j(1 − u_j − d_j) + π_{j+1}d_{j+1} = π_j を満たす（定常）。
      `ratio_form`：上下法では u_j = 1 − P(x_j)^k、d_j = P(x_j)^k なので
      π(x + δ)/π(x) = (1 − P(x)^k)/P(x + δ)^k（確かめの係の閉じた形）。
      `pi_product`：π_j = π_0 Π_{i<j} u_i/d_{i+1} と置けば詳細釣り合いを満たす。
  (4) `balance_point`：上がる確率と下がる確率が等しい ⇔ P^k = 1/2 ⇔ P = (1/2)^(1/k)。
足した仮定：一歩が終わるたびに「続けて正しい数」が 0 に戻るので、一歩の向きはその場所での新しい
試行の列だけで決まる（鎖が出生死滅になること）を模型として置いた。
形式化していないもの：ずれの係数 C（歩幅 → 0 の漸近、試行ごとの重み付き平均）、正規分布の観察者で
k = 1 のとき C = 0 になること、乱数の表、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper935

open Finset Real

/-- (1) 一歩の向き：途中で誤る確率の和 + k 回正しい確率 = 1。 -/
theorem step_probs (P : ℝ) (k : ℕ) :
    ∑ m ∈ range k, P ^ m * (1 - P) + P ^ k = 1 := by
  induction k with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

/-- (2) 一歩にかかる試行の数の期待値は 1 + P + … + P^(k−1)。 -/
theorem expected_trials (P : ℝ) (k : ℕ) :
    ∑ m ∈ range k, ((m : ℝ) + 1) * (P ^ m * (1 - P)) + k * P ^ k = ∑ m ∈ range k, P ^ m := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    push_cast
    rw [pow_succ]
    linarith

/-- (3) 詳細釣り合いなら、各点の釣り合いの式が成り立つ（定常）。 -/
theorem detailed_balance_stationary (w u d : ℤ → ℝ)
    (hdb : ∀ j, w (j + 1) * d (j + 1) = w j * u j) (j : ℤ) :
    w (j - 1) * u (j - 1) + w j * (1 - u j - d j) + w (j + 1) * d (j + 1) = w j := by
  have h1 := hdb (j - 1)
  rw [sub_add_cancel] at h1
  have h2 := hdb j
  linarith

/-- (3) 上下法の比の形：π(x + δ)/π(x) = (1 − P(x)^k)/P(x + δ)^k。 -/
theorem ratio_form (w : ℤ → ℝ) (P : ℤ → ℝ) (k : ℕ) (hP : ∀ j, 0 < P j) (hw : ∀ j, 0 < w j)
    (hdb : ∀ j, w (j + 1) * P (j + 1) ^ k = w j * (1 - P j ^ k)) (j : ℤ) :
    w (j + 1) / w j = (1 - P j ^ k) / P (j + 1) ^ k := by
  have := hdb j
  have h1 := hw j
  have h2 : 0 < P (j + 1) ^ k := pow_pos (hP _) k
  rw [div_eq_div_iff (ne_of_gt h1) (ne_of_gt h2)]
  linarith

/-- (3) 積の形の π は詳細釣り合いを満たす（片側の格子 j = 0, 1, 2, …）。 -/
noncomputable def piProd (π₀ : ℝ) (u d : ℕ → ℝ) : ℕ → ℝ
  | 0 => π₀
  | j + 1 => piProd π₀ u d j * u j / d (j + 1)

theorem pi_product (π₀ : ℝ) (u d : ℕ → ℝ) (hd : ∀ j, d (j + 1) ≠ 0) (j : ℕ) :
    piProd π₀ u d (j + 1) * d (j + 1) = piProd π₀ u d j * u j := by
  simp only [piProd]; rw [div_mul_cancel₀ _ (hd j)]

/-- (4) 釣り合いの点：P^k = 1 − P^k ⇔ P = (1/2)^(1/k)（0 ≤ P、k ≥ 1）。 -/
theorem balance_point {P : ℝ} (hP : 0 ≤ P) {k : ℕ} (hk : 1 ≤ k) :
    P ^ k = 1 - P ^ k ↔ P = (1 / 2 : ℝ) ^ (1 / (k : ℝ)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  constructor
  · intro h
    have h2 : P ^ k = 1 / 2 := by linarith
    rw [← h2, ← rpow_natCast, ← rpow_mul hP, mul_one_div_cancel hk', rpow_one]
  · intro h
    have : P ^ k = 1 / 2 := by
      rw [h, ← rpow_natCast, ← rpow_mul (by norm_num), one_div_mul_cancel hk', rpow_one]
    linarith

end Paper935

end Yamagishi
