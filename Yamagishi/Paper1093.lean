/-
論文1093『ブラックホールのエントロピーは 3 次元で地平線の円盤、影の円盤は 27/4 倍大きい』の
数学の部分を、一般の次元で機械に確かめさせる（格上げ）。

原稿（1093_yamagishi_bh_entropy_is_the_horizon_disk_in_3d_…/…_jp.tex）の
  第2節：タンゲルリーニの解で M = (d−1)S_{d−1} r^(d−2)/(16πG)、T = (d−2)/(4πr)、S = S_{d−1} r^(d−1)/(4G)。
    第一法則 dM = T dS を d = 3〜10 と三つの半径で数値で確かめた。
  第3節：作用の G で、エントロピーの係数 S_{d−1}/4 が断面 V_{d−1} と同じ数になるのは
    d = 3〜10 のうち 3 次元だけ（数え上げ）。
  第4節：ニュートンの G で係数 2π(d−2)/(d−1) が V_{d−1} と同じになるのは 3 次元と 4 次元だけ。
    漸化式 V_{d−1} = 2πV_{d−3}/(d−1) で d − 2 = V_{d−3} に帰着し、「V_k = k + 1 は k = 0, 1 だけ、
    k ≥ 2 の球は π を持つ」と書く（π の大小か超越性を明記していない、と確かめの係が指摘）。
  第5節：8πG = 1 なら S = 2πA。第6節：影の衝突径数 3√3 M、影の円盤は地平線の断面の 27/4 倍。

ここで証明した一般の言明（d は自然数）：
  (1) 第一法則 dM/dr = T dS/dr（d は任意の実数、r > 0）。
  (2) ニュートンの G での一致：d ≥ 3 で 2π(d−2)/(d−1) = V_{d−1} ⇔ d = 3 または d = 4。
      途中の V_k = k + 1 ⇔ k = 0 または 1 は、π の大小 3 < π < 3.15 だけを使って、すべての k で示した
      （k = 2, 3 は π ≠ 3、k ≥ 4 は V_k < k + 1 を漸化式の帰納法で）。π の超越性は要らない。
  (3) 作用の G での一致：d ≥ 1 で S_{d−1}/4 = V_{d−1} ⇔ d = 3（すべての d）。
      比 Q_m = (m+1)V_{m+1}/V_m が Q_{m+2} = ((m+2)/(m+1)) Q_m を満たして一つ飛びに増えることから示した
      （確かめの係の「比が d について増える」は一つ飛びに増える、が正確）。
  (4) G_N の置き方から S = 2π(d−2)/(d−1) · r^(d−1)/G_N（代数）、8πG = 1 で S = 2πA。
  (5) 影：r > 2M で r²/(1 − 2M/r) の最小は r = 3M での 27M²、影の円盤 ÷ 地平線の断面 = 27/4。
足した仮定：(2) の S_{d−1} = d·V_d と V の漸化式は、論文912 のファイルの定義と定理をそのまま使った。
G_N/G = 8π(d−2)/((d−1)S_{d−1}) は原稿が解の加速度から測った関係で、ここでは置き方として入力に置いた。

形式化していないもの：タンゲルリーニの解そのもの（M・T・S の式は入力）、表面重力の物理、
光が回れる円の動力学（b = r/√f の形は入力）、アルキメデスの 4 の読み、殻ごとの一致の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper912

namespace Yamagishi

namespace Paper1093

open Real Set
open Yamagishi.Paper912 (V V_zero V_one V_two V_three V_succ_succ)

/-! ### (1) 第一法則 -/

/-- (1) M = (d−1)S r^(d−2)/(16πG)、T = (d−2)/(4πr)、S(r) = S r^(d−1)/(4G) で dM/dr = T · dS/dr。 -/
theorem first_law (d Sd G r : ℝ) (hG : G ≠ 0) (hr : 0 < r) :
    HasDerivAt (fun r => (d - 1) * Sd * r ^ (d - 2) / (16 * π * G))
      ((d - 2) / (4 * π * r) * ((d - 1) * Sd * r ^ (d - 2) / (4 * G))) r ∧
    HasDerivAt (fun r => Sd * r ^ (d - 1) / (4 * G)) ((d - 1) * Sd * r ^ (d - 2) / (4 * G)) r := by
  have h2 : HasDerivAt (fun r : ℝ => r ^ (d - 2)) ((d - 2) * r ^ (d - 2 - 1)) r :=
    hasDerivAt_rpow_const (Or.inl hr.ne')
  have h1 : HasDerivAt (fun r : ℝ => r ^ (d - 1)) ((d - 1) * r ^ (d - 1 - 1)) r :=
    hasDerivAt_rpow_const (Or.inl hr.ne')
  have e : r ^ (d - 2 - 1) = r ^ (d - 2) / r := by rw [rpow_sub hr, rpow_one]
  have e' : d - 1 - 1 = d - 2 := by ring
  constructor
  · have := (h2.const_mul ((d - 1) * Sd)).div_const (16 * π * G)
    convert this using 1
    rw [e]
    field_simp
    ring
  · have := (h1.const_mul Sd).div_const (4 * G)
    convert this using 1
    rw [e']
    ring

/-! ### (2) ニュートンの G：3 次元と 4 次元だけ -/

theorem V_four : V 4 = π ^ 2 / 2 := by
  have h := V_succ_succ 2; rw [V_two] at h; norm_num at h; rw [h]; field_simp; ring

theorem V_five : V 5 = 8 * π ^ 2 / 15 := by
  have h := V_succ_succ 3; rw [V_three] at h; norm_num at h; rw [h]; field_simp; ring

/-- k ≥ 4 では V_k < k + 1（漸化式と π < 3.15 による帰納法）。 -/
theorem V_lt_succ (j : ℕ) : V (j + 4) < (j : ℝ) + 5 ∧ V (j + 5) < (j : ℝ) + 6 := by
  have hp1 := pi_gt_three
  have hp2 := pi_lt_d2
  induction j with
  | zero =>
    rw [V_four, V_five]
    constructor <;> nlinarith
  | succ j ih =>
    refine ⟨by simpa [add_assoc] using ih.2.trans_le (by linarith), ?_⟩
    have hrec : V (j + 1 + 5) = 2 * π / ((j + 4 : ℕ) + 2) * V (j + 4) := by
      rw [show j + 1 + 5 = (j + 4) + 2 by ring, V_succ_succ]
    rw [hrec]
    have hV0 : 0 ≤ V (j + 4) := by
      unfold V; exact div_nonneg (by positivity) (Gamma_pos_of_pos (by positivity)).le
    have hpos : (0 : ℝ) < ((j + 4 : ℕ) : ℝ) + 2 := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    push_cast
    nlinarith [ih.1]

/-- V_k = k + 1 ⇔ k = 0 または k = 1（すべての k）。 -/
theorem V_eq_succ_iff (k : ℕ) : V k = (k : ℝ) + 1 ↔ k = 0 ∨ k = 1 := by
  constructor
  · intro h
    match k, h with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr rfl
    | 2, h => rw [V_two] at h; push_cast at h; linarith [pi_gt_d2]
    | 3, h => rw [V_three] at h; push_cast at h; linarith [pi_gt_d2]
    | j + 4, h =>
      exfalso
      have := (V_lt_succ j).1
      push_cast at h
      linarith
  · rintro (rfl | rfl)
    · simp [V_zero]
    · rw [V_one]; norm_num

/-- (2) ニュートンの G での一致：d ≥ 3 で 2π(d−2)/(d−1) = V_{d−1} ⇔ d = 3 または d = 4。
d = k + 3 と書く。 -/
theorem newton_G_match (k : ℕ) :
    2 * π * ((k : ℝ) + 1) / ((k : ℝ) + 2) = V (k + 2) ↔ k = 0 ∨ k = 1 := by
  rw [V_succ_succ, ← V_eq_succ_iff]
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  have hπ : 2 * π ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_left_inj₀ h2]
  constructor
  · intro h; exact (mul_left_cancel₀ hπ h).symm
  · intro h; rw [h]

/-! ### (3) 作用の G：3 次元だけ -/

/-- 比 Q_m = (m+1)V_{m+1}/V_m（S_m/V_m、S_m は m+1 次元の単位球面の面積）。 -/
noncomputable def Q (m : ℕ) : ℝ := (m + 1) * V (m + 1) / V m

theorem V_pos (m : ℕ) : 0 < V m := by
  unfold V; exact div_pos (by positivity) (Gamma_pos_of_pos (by positivity))

/-- Q は一つ飛びに増える：Q_{m+2} = ((m+2)/(m+1)) Q_m。 -/
theorem Q_rec (m : ℕ) : Q (m + 2) = ((m : ℝ) + 2) / ((m : ℝ) + 1) * Q m := by
  unfold Q
  have e1 : V (m + 2 + 1) = 2 * π / ((m + 1 : ℕ) + 2) * V (m + 1) := by
    rw [show m + 2 + 1 = (m + 1) + 2 by ring, V_succ_succ]
  rw [e1, V_succ_succ]
  have := V_pos m
  have := V_pos (m + 1)
  have hπ := pi_pos
  push_cast
  field_simp
  ring

theorem Q_zero : Q 0 = 2 := by unfold Q; rw [V_one]; norm_num [V_zero]
theorem Q_one : Q 1 = π := by unfold Q; rw [V_two, V_one]; norm_num
theorem Q_two : Q 2 = 4 := by
  unfold Q; rw [V_three, V_two]; have := pi_pos; norm_num; field_simp

/-- m ≥ 3 では Q_m > 4。 -/
theorem Q_gt_four (j : ℕ) : 4 < Q (j + 3) ∧ 4 < Q (j + 4) := by
  induction j with
  | zero =>
    have h3 : Q 3 = 3 / 2 * Q 1 := by rw [show (3 : ℕ) = 1 + 2 by rfl, Q_rec]; norm_num
    have h4 : Q 4 = 4 / 3 * Q 2 := by rw [show (4 : ℕ) = 2 + 2 by rfl, Q_rec]; norm_num
    rw [h3, h4, Q_one, Q_two]
    constructor <;> nlinarith [pi_gt_d2]
  | succ j ih =>
    refine ⟨by simpa [add_assoc] using ih.2, ?_⟩
    have h := Q_rec (j + 3)
    rw [show j + 3 + 2 = j + 1 + 4 by ring] at h
    rw [h]
    have hpos : (0 : ℝ) < (((j + 3 : ℕ) : ℝ) + 1) := by positivity
    have hge : (1 : ℝ) ≤ (((j + 3 : ℕ) : ℝ) + 2) / (((j + 3 : ℕ) : ℝ) + 1) := by
      rw [le_div_iff₀ hpos]; linarith
    nlinarith [ih.1]

/-- (3) 作用の G での一致：S_{d−1}/4 = V_{d−1}、つまり d·V_d/4 = V_{d−1} ⇔ d = 3（d = m + 1 ≥ 1）。 -/
theorem action_G_match (m : ℕ) : ((m : ℝ) + 1) * V (m + 1) / 4 = V m ↔ m = 2 := by
  have hV := V_pos m
  have hQ : ((m : ℝ) + 1) * V (m + 1) / 4 = V m ↔ Q m = 4 := by
    unfold Q
    constructor
    · intro h; field_simp; linarith
    · intro h; field_simp at h; linarith
  rw [hQ]
  constructor
  · intro h
    match m, h with
    | 0, h => rw [Q_zero] at h; norm_num at h
    | 1, h => rw [Q_one] at h; linarith [pi_lt_d2]
    | 2, _ => rfl
    | j + 3, h => exact absurd h (Q_gt_four j).1.ne'
  · rintro rfl; exact Q_two

/-! ### (4) 置き方の代数 -/

/-- (4) G = G_N(d−1)S_{d−1}/(8π(d−2)) を入れると
S = S_{d−1}r^(d−1)/(4G) = 2π(d−2)/(d−1) · r^(d−1)/G_N。 -/
theorem newton_entropy (d Sd GN rr : ℝ) (hd1 : d - 1 ≠ 0) (hd2 : d - 2 ≠ 0) (hS : Sd ≠ 0)
    (hGN : GN ≠ 0) :
    Sd * rr / (4 * (GN * (d - 1) * Sd / (8 * π * (d - 2)))) =
      2 * π * (d - 2) / (d - 1) * rr / GN := by
  have := pi_pos
  field_simp
  ring

/-- (4) 8πG = 1 なら S = A/(4G) = 2πA。 -/
theorem eight_pi_G_one (A : ℝ) : A / (4 * (1 / (8 * π))) = 2 * π * A := by
  have := pi_pos
  field_simp
  ring

/-! ### (5) 影の円盤 -/

/-- (5) r > 2M で r²/(1 − 2M/r) ≥ 27M²、等号は r = 3M（影の縁の衝突径数 b = 3√3 M）。 -/
theorem shadow_min (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    27 * M ^ 2 ≤ r ^ 2 / (1 - 2 * M / r) ∧ (3 * M) ^ 2 / (1 - 2 * M / (3 * M)) = 27 * M ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hden : 0 < 1 - 2 * M / r := by
    rw [sub_pos, div_lt_one hr0]; exact hr
  constructor
  · rw [le_div_iff₀ hden]
    have key : r ^ 3 - 27 * M ^ 2 * r + 54 * M ^ 3 = (r - 3 * M) ^ 2 * (r + 6 * M) := by ring
    have : 0 ≤ (r - 3 * M) ^ 2 * (r + 6 * M) := by positivity
    have e : 27 * M ^ 2 * (1 - 2 * M / r) = (27 * M ^ 2 * r - 54 * M ^ 3) / r := by
      field_simp; ring
    rw [e, div_le_iff₀ hr0]
    nlinarith
  · field_simp; ring

/-- (5) 影の円盤 π(3√3M)² と地平線の断面 π(2M)² の比は 27/4。 -/
theorem shadow_ratio (M : ℝ) (hM : 0 < M) : π * (27 * M ^ 2) / (π * (2 * M) ^ 2) = 27 / 4 := by
  have := pi_pos
  field_simp
  ring

end Paper1093

end Yamagishi
