/-
論文360『厳密な式が計算できないとき、途中で切ると上下から挟める』の格上げ（一般の形）。

原稿（360_yamagishi_exact_is_not_computable_but_truncation_brackets/…_jp.tex）は、撹乱順列の確率の
包除の和を k = 0〜8 と 12 で打ち切り、極限値 1/e に対して上下が交互になる表を出し、
|S₅ − S₆| = 1/6! を確かめている。すべての n と k で挟むことは示していない。

ここで証明した言明（S_k = Σ_{j=0}^{k} (−1)^j/j!）：
  (1) `derangement_ratio`：すべての n で D_n/n! = S_n（D_n は撹乱順列の数。Mathlib の
      `numDerangements_sum` から）。
  (2) `alt_tail_nonneg`・`alt_tail_le`・`alt_tail_pos`（部品）：単調に減る非負の列 a の交代和
      Σ_{i<L} (−1)^i a(m + i) は 0 と a(m) のあいだにあり、a が狭義に減って正なら L ≥ 1 で正。
  (3) `bracket`：すべての n と 0 ≤ k ≤ n で (−1)^k (S_k − D_n/n!) ≥ 0（k が偶数なら上から、奇数なら
      下から挟む）。`bracket_eq_zero_iff`：等号は k = n のときだけ。
      `bracket_gap`：挟みの幅は 1/(k+1)! 以下（|S_k − D_n/n!| ≤ 1/(k+1)!）。
  (4) `bonferroni_none`：一般の形（ボンフェローニの不等式、どれも起きない側）：有限集合 α の部分集合の
      族 S_i（i ∈ s）について、どれにも入らない点の数 N₀ と、包除の和を大きさ k までの部分族で
      打ち切った B_k は (−1)^k (B_k − N₀) ≥ 0 を満たす。
注意：上か下かの向きは、何を数えるかで逆になる。原稿の「偶数で上」は、どれも起きない割合
（S₀ = 1 から始める形）での言い方で、和事象 |∪S_i| を S₁ − S₂ + … で切る形では奇数で上になる。
形式化していないもの：極限値 1/e との比較（原稿の表は 1/e と比べている）、計算の時間の換算。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper360

open Finset

/-- 打ち切りの和 S_k = Σ_{j=0}^{k} (−1)^j/j!。 -/
noncomputable def S (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)

/-- (1) D_n/n! = S_n。 -/
theorem derangement_ratio (n : ℕ) : (numDerangements n : ℝ) / (n.factorial : ℝ) = S n := by
  have h := numDerangements_sum n
  have hz : (numDerangements n : ℝ) =
      ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * ((k + 1).ascFactorial (n - k) : ℝ) := by
    exact_mod_cast h
  rw [hz, S, sum_div]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have hf : (k.factorial : ℝ) * ((k + 1).ascFactorial (n - k) : ℝ) = n.factorial := by
    have := Nat.factorial_mul_ascFactorial k (n - k)
    rw [Nat.add_sub_cancel' hkn] at this
    exact_mod_cast this
  have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
  have hn0 : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [← hf]
  field_simp

/-- 交代和 T(m, L) = Σ_{i<L} (−1)^i a(m + i)。 -/
noncomputable def T (a : ℕ → ℝ) (m L : ℕ) : ℝ := ∑ i ∈ range L, (-1 : ℝ) ^ i * a (m + i)

theorem T_succ (a : ℕ → ℝ) (m L : ℕ) : T a m (L + 1) = a m - T a (m + 1) L := by
  unfold T
  rw [sum_range_succ', pow_zero, one_mul, add_zero, sub_eq_add_neg, ← sum_neg_distrib, add_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [pow_succ, show m + (i + 1) = m + 1 + i by ring]; ring

/-- (2) 交代和は 0 と a(m) のあいだ。 -/
theorem alt_tail_bounds {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (L : ℕ) :
    ∀ m, 0 ≤ T a m L ∧ T a m L ≤ a m := by
  induction L with
  | zero => intro m; simp [T, h0 m]
  | succ L ih =>
    intro m
    rw [T_succ]
    obtain ⟨h1, h2⟩ := ih (m + 1)
    have := ha (Nat.le_succ m)
    constructor <;> linarith

theorem alt_tail_nonneg {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (m L : ℕ) :
    0 ≤ T a m L := (alt_tail_bounds ha h0 L m).1

theorem alt_tail_le {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (m L : ℕ) :
    T a m L ≤ a m := (alt_tail_bounds ha h0 L m).2

/-- (2) 狭義に減る正の列なら、L ≥ 1 で交代和は正。 -/
theorem alt_tail_pos {a : ℕ → ℝ} (ha : StrictAnti a) (h0 : ∀ i, 0 < a i) (m L : ℕ) :
    0 < T a m (L + 1) := by
  rw [T_succ]
  have := alt_tail_le ha.antitone (fun i => (h0 i).le) (m + 1) L
  have := ha (Nat.lt_succ_self m)
  linarith

/-- 1/j! の列。 -/
noncomputable def invFact (j : ℕ) : ℝ := 1 / (j.factorial : ℝ)

theorem invFact_strictAnti : StrictAnti (fun j => invFact (j + 1)) := by
  apply strictAnti_nat_of_succ_lt
  intro j
  unfold invFact
  apply one_div_lt_one_div_of_lt (by positivity)
  have : ((j + 1).factorial : ℝ) < ((j + 1 + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ (j + 1)]; push_cast
    have : (0 : ℝ) < (j + 1).factorial := by positivity
    nlinarith
  exact this

theorem invFact_pos (j : ℕ) : 0 < invFact j := by unfold invFact; positivity

/-- (−1)^k (S_k − S_n) は 1/(k+1)! から始まる交代和。 -/
theorem bracket_eq_T {k n : ℕ} (hkn : k ≤ n) :
    (-1 : ℝ) ^ k * (S k - S n) = T (fun j => invFact (j + 1)) k (n - k) := by
  have hsplit : n + 1 = (k + 1) + (n - k) := by omega
  have hsum : S n = S k + ∑ i ∈ range (n - k), (-1 : ℝ) ^ (k + 1 + i) /
      ((k + 1 + i).factorial : ℝ) := by
    unfold S
    rw [hsplit, Finset.sum_range_add (fun j => (-1 : ℝ) ^ j / (j.factorial : ℝ)) (k + 1) (n - k)]
  rw [hsum, sub_add_cancel_left, mul_neg, mul_sum, ← sum_neg_distrib]
  unfold T invFact
  apply sum_congr rfl
  intro i _
  have hkk : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [show k + 1 + i = k + i + 1 by ring, pow_succ, pow_add, div_eq_mul_inv]
  show _ = (-1 : ℝ) ^ i * (1 / ((k + i + 1).factorial : ℝ))
  rw [one_div]
  linear_combination ((-1 : ℝ) ^ i * (((k + i + 1).factorial : ℝ))⁻¹) * hkk

/-- (3) 交互に上下から挟む。 -/
theorem bracket {k n : ℕ} (hkn : k ≤ n) :
    0 ≤ (-1 : ℝ) ^ k * (S k - (numDerangements n : ℝ) / (n.factorial : ℝ)) := by
  rw [derangement_ratio, bracket_eq_T hkn]
  exact alt_tail_nonneg invFact_strictAnti.antitone (fun j => (invFact_pos _).le) _ _

/-- (3) 等号は k = n のときだけ。 -/
theorem bracket_eq_zero_iff {k n : ℕ} (hkn : k ≤ n) :
    (-1 : ℝ) ^ k * (S k - (numDerangements n : ℝ) / (n.factorial : ℝ)) = 0 ↔ k = n := by
  rw [derangement_ratio, bracket_eq_T hkn]
  constructor
  · intro h
    by_contra hne
    obtain ⟨L, hL⟩ : ∃ L, n - k = L + 1 := ⟨n - k - 1, by omega⟩
    rw [hL] at h
    have := alt_tail_pos invFact_strictAnti (fun i => invFact_pos (i + 1)) k L
    linarith
  · rintro rfl
    simp [T]

/-- (3) 挟みの幅は 1/(k+1)! 以下。 -/
theorem bracket_gap {k n : ℕ} (hkn : k ≤ n) :
    |S k - (numDerangements n : ℝ) / (n.factorial : ℝ)| ≤ 1 / ((k + 1).factorial : ℝ) := by
  rw [derangement_ratio]
  have h1 := bracket_eq_T hkn
  have hle := alt_tail_le invFact_strictAnti.antitone (fun j => (invFact_pos _).le) k (n - k)
  have hnn := alt_tail_nonneg invFact_strictAnti.antitone (fun j => (invFact_pos _).le) k (n - k)
  rw [← h1] at hle hnn
  have habs : |(-1 : ℝ) ^ k| = 1 := by simp
  have : |S k - S n| = (-1 : ℝ) ^ k * (S k - S n) := by
    rw [← abs_of_nonneg hnn, abs_mul, habs, one_mul]
  rw [this]
  simpa [invFact] using hle

/-! ### 一般の形：ボンフェローニの不等式（どれも起きない側） -/

/-- 二項係数の交代の部分和。 -/
theorem alt_choose_partial (j k : ℕ) :
    (∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i * (j.choose i : ℤ))) =
      if j = 0 then 1 else (-1) ^ k * ((j - 1).choose k : ℤ) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [sum_range_succ', Nat.choose_zero_succ]
  · simp only [hj.ne', ↓reduceIte]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Int.alternating_sum_range_choose_eq_choose]
    simp

section Bonferroni

variable {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]

/-- 大きさ k までの部分族で打ち切った包除の和 B_k。 -/
def Bk (s : Finset ι) (S : ι → Finset α) (k : ℕ) : ℤ :=
  ∑ t ∈ s.powerset.filter (fun t => t.card ≤ k), (-1 : ℤ) ^ t.card * ((t.inf S).card : ℤ)

/-- 点 x を含む S_i の添え字。 -/
def idx (s : Finset ι) (S : ι → Finset α) (x : α) : Finset ι := s.filter (fun i => x ∈ S i)

omit [DecidableEq ι] in
theorem sum_filter_card_le (u : Finset ι) (k : ℕ) :
    (∑ t ∈ u.powerset.filter (fun t => t.card ≤ k), (-1 : ℤ) ^ t.card) =
      ∑ m ∈ range (k + 1), (-1 : ℤ) ^ m * (u.card.choose m : ℤ) := by
  rw [sum_filter]
  have := sum_powerset_apply_card (fun m => if m ≤ k then (-1 : ℤ) ^ m else 0) (x := u)
  rw [this]
  set N := u.card
  have h1 : (∑ m ∈ range (N + 1), N.choose m • (if m ≤ k then (-1 : ℤ) ^ m else 0)) =
      ∑ m ∈ range (N + k + 1), (if m ≤ k then (-1 : ℤ) ^ m * (N.choose m : ℤ) else 0) := by
    rw [sum_congr rfl (fun m _ => show N.choose m • (if m ≤ k then (-1 : ℤ) ^ m else 0) =
      (if m ≤ k then (-1 : ℤ) ^ m * (N.choose m : ℤ) else 0) by
        split_ifs <;> simp [mul_comm])]
    apply sum_subset (fun m hm => by simp at hm ⊢; omega)
    intro m _ hm
    simp at hm
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have h2 : (∑ m ∈ range (k + 1), (-1 : ℤ) ^ m * (N.choose m : ℤ)) =
      ∑ m ∈ range (N + k + 1), (if m ≤ k then (-1 : ℤ) ^ m * (N.choose m : ℤ) else 0) := by
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext m; simp; omega
  rw [h1, h2]

theorem card_inf_eq (s : Finset ι) (S : ι → Finset α) {t : Finset ι} (ht : t ⊆ s) :
    ((t.inf S).card : ℤ) = ∑ x : α, if t ⊆ idx s S x then 1 else 0 := by
  rw [sum_boole]
  congr 2
  ext x
  rw [Finset.mem_inf, Finset.mem_filter]
  simp only [mem_univ, true_and, idx, Finset.subset_iff, Finset.mem_filter]
  constructor
  · intro h i hi
    exact ⟨ht hi, h i hi⟩
  · intro h i hi
    exact (h hi).2

/-- B_k を点ごとの和に書き直す。 -/
theorem Bk_eq (s : Finset ι) (S : ι → Finset α) (k : ℕ) :
    Bk s S k = ∑ x : α, ∑ m ∈ range (k + 1), (-1 : ℤ) ^ m * ((idx s S x).card.choose m : ℤ) := by
  unfold Bk
  rw [sum_congr rfl (fun t ht => by
    rw [card_inf_eq s S (mem_powerset.1 (mem_filter.1 ht).1)])]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← sum_filter_card_le]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨⟨-, hk⟩, hx⟩; exact ⟨hx, hk⟩
  · rintro ⟨hx, hk⟩
    exact ⟨⟨hx.trans (filter_subset _ _), hk⟩, hx⟩

omit [DecidableEq ι] in
/-- どれにも入らない点の数 N₀。 -/
theorem N0_eq (s : Finset ι) (S : ι → Finset α) :
    ((s.inf fun i => (S i)ᶜ).card : ℤ) = ∑ x : α, if (idx s S x).card = 0 then 1 else 0 := by
  rw [sum_boole]
  congr 2
  ext x
  simp only [Finset.mem_inf, mem_compl, mem_filter, mem_univ, true_and, card_eq_zero,
    idx, filter_eq_empty_iff]

/-- (4) ボンフェローニの不等式（どれも起きない側）：(−1)^k (B_k − N₀) ≥ 0。 -/
theorem bonferroni_none (s : Finset ι) (S : ι → Finset α) (k : ℕ) :
    0 ≤ (-1 : ℤ) ^ k * (Bk s S k - ((s.inf fun i => (S i)ᶜ).card : ℤ)) := by
  rw [Bk_eq, N0_eq, ← sum_sub_distrib, mul_sum]
  apply sum_nonneg
  intro x _
  rw [alt_choose_partial]
  split_ifs with h
  · simp
  · have hkk : ((-1 : ℤ) ^ k) * ((-1) ^ k) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [sub_zero, ← mul_assoc, hkk, one_mul]
    positivity

end Bonferroni

end Paper360

end Yamagishi
