/-
論文638『3×3 の魔方陣は中心が 5 で一つだけ、4×4 はどのマスも決まらず 880 ある』の格上げ（一部の一般の形）。

日本語の一文：どの次数でも、すべての魔方陣で同じ数が入るマスがあれば、その数は (n² + 1)/2 に限られる
（数 x を n² + 1 − x に替えた補数の方陣も魔方陣だから）ので、偶数の次数ではどのマスも決まらず、3 次では
中心がいつも 5 で、ほかのマスは決まらず、4・5・6 次ではどのマスも決まらない。
English: For every order n, a cell that holds the same number in all magic squares must hold
(n² + 1)/2, because replacing x by n² + 1 − x gives another magic square; hence no cell is fixed for
even n (once a square exists), the 3×3 centre is always 5 and no other 3×3 cell is fixed, and no
cell is fixed for n = 4, 5, 6.

原稿（638_yamagishi_the_3x3_magic_square_fixes_its_centre_the_4x4_fixes_no_cell/…_jp.tex）は、3×3 を
全 362880 通りで調べて 8 個・中心はいつも 5、4×4 を後戻り探索で 7040 個・どのマスにも 16 種類、5×5 は
中心を通る四本が 17 マスしか覆わないことだけ、6×6 は一例を示している。5×5 の中心が動くことは
示していない。

ここで証明した言明（魔方陣は 1 から n² を一度ずつ使い、行・列・二本の対角線の和が n(n² + 1)/2）：
  (1) `complement_isMagic`：魔方陣の補数 n² + 1 − x も魔方陣。
      `fixed_value`：すべての魔方陣で同じ数 v が入るマスがあり、魔方陣が一つでも在るなら、2v = n² + 1。
      `not_fixed`：魔方陣 M のマスで 2M(i, j) ≠ n² + 1 なら、そのマスの数が違う魔方陣が在る。
      `even_not_fixed`：n が偶数なら、魔方陣が一つ在ればどのマスも決まらない。
  (2) `center_three`：3×3 で行・列・対角線の和が 15 なら（数が違うことも使わずに）中心は 5。
      `three_others_not_fixed`：3×3 の中心以外のマスは決まらない（洛書とその補数）。
  (3) `four_not_fixed`：原稿の 4A + B + 1 の 4×4 は魔方陣で、どのマスも決まらない。
      `five_not_fixed`：5×5 の線形の方陣 5((i + 2j) mod 5) + ((2i + j) mod 5) + 1（中心 7）と、その行を
      一つずらした方陣はどちらも魔方陣で、中心を含めどのマスも決まらない。
      `six_not_fixed`：原稿の 6×6 は魔方陣で、どのマスも決まらない。
足した仮定：なし。具体の方陣が魔方陣であることは `decide` で確かめた（小さな有限の確かめ）。
形式化していないもの：7 以上の奇数の次数（下読みの AI の案のシャム法と縁取りの構成）と、8 以上の偶数の
次数での魔方陣の存在。したがって「すべての n で、決まるマスは 3 次の中心だけ」は n ≤ 6 までと、偶数の
次数では存在を仮定した形までしか通していない。8 個・7040 個・880 個の数え上げも形式化していない。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper638

open Finset

/-- n 次の魔方陣（数は整数で置く）：1 から n² を一度ずつ使い、行・列・二本の対角線の和の 2 倍が
n(n² + 1)。 -/
def IsMagic (n : ℕ) (M : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, 1 ≤ M i j ∧ M i j ≤ (n : ℤ) ^ 2) ∧
  Function.Injective (fun p : Fin n × Fin n => M p.1 p.2) ∧
  (∀ i, 2 * ∑ j, M i j = n * (n ^ 2 + 1)) ∧
  (∀ j, 2 * ∑ i, M i j = n * (n ^ 2 + 1)) ∧
  (2 * ∑ i, M i i = n * (n ^ 2 + 1)) ∧
  (2 * ∑ i, M i (Fin.rev i) = n * (n ^ 2 + 1))

instance (n : ℕ) (M : Fin n → Fin n → ℤ) : Decidable (IsMagic n M) := by
  unfold IsMagic; infer_instance

/-- 補数の方陣 n² + 1 − M。 -/
def compl (n : ℕ) (M : Fin n → Fin n → ℤ) : Fin n → Fin n → ℤ :=
  fun i j => (n : ℤ) ^ 2 + 1 - M i j

theorem sum_compl (n : ℕ) (f : Fin n → ℤ) :
    2 * ∑ i, ((n : ℤ) ^ 2 + 1 - f i) = 2 * (n * ((n : ℤ) ^ 2 + 1)) - 2 * ∑ i, f i := by
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- (1) 補数も魔方陣。 -/
theorem complement_isMagic {n : ℕ} {M : Fin n → Fin n → ℤ} (h : IsMagic n M) :
    IsMagic n (compl n M) := by
  obtain ⟨hr, hi, hrow, hcol, hd, ha⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; unfold compl; constructor <;> linarith [hr i j]
  · intro p q hpq
    simp only [compl] at hpq
    exact hi (show M p.1 p.2 = M q.1 q.2 by linarith)
  · intro i; unfold compl; rw [sum_compl, hrow i]; ring
  · intro j; unfold compl; rw [sum_compl, hcol j]; ring
  · unfold compl; rw [sum_compl, hd]; ring
  · unfold compl; rw [sum_compl, ha]; ring

/-- (1) 決まるマスの数は (n² + 1)/2。 -/
theorem fixed_value {n : ℕ} {i j : Fin n} {v : ℤ}
    (hfix : ∀ M, IsMagic n M → M i j = v) (hex : ∃ M, IsMagic n M) :
    2 * v = (n : ℤ) ^ 2 + 1 := by
  obtain ⟨M, hM⟩ := hex
  have h1 := hfix M hM
  have h2 := hfix _ (complement_isMagic hM)
  simp only [compl] at h2
  linarith

/-- (1) 2M(i, j) ≠ n² + 1 なら、そのマスの数が違う魔方陣（補数）が在る。 -/
theorem not_fixed {n : ℕ} {M : Fin n → Fin n → ℤ} (hM : IsMagic n M) {i j : Fin n}
    (h : 2 * M i j ≠ (n : ℤ) ^ 2 + 1) :
    ∃ M', IsMagic n M' ∧ M' i j ≠ M i j :=
  ⟨compl n M, complement_isMagic hM, by simp only [compl]; intro h'; apply h; linarith⟩

/-- (1) n が偶数なら、魔方陣が一つ在ればどのマスも決まらない。 -/
theorem even_not_fixed {n : ℕ} (hn : Even n) {M : Fin n → Fin n → ℤ} (hM : IsMagic n M)
    (i j : Fin n) : ∃ M', IsMagic n M' ∧ M' i j ≠ M i j := by
  apply not_fixed hM
  obtain ⟨k, rfl⟩ := hn
  intro h
  have : (2 : ℤ) * (M i j - 2 * k ^ 2) = 1 := by push_cast at h; linarith
  omega

/-- (2) 3×3 で行・列・対角線の和が 15 なら中心は 5（数が違うことは使わない）。 -/
theorem center_three (M : Fin 3 → Fin 3 → ℤ) (hrow : ∀ i, ∑ j, M i j = 15)
    (hcol : ∀ j, ∑ i, M i j = 15) (hd : ∑ i, M i i = 15)
    (ha : ∑ i, M i (Fin.rev i) = 15) : M 1 1 = 5 := by
  have r0 := hrow 0; have r1 := hrow 1; have r2 := hrow 2
  have c1 := hcol 1
  simp only [Fin.sum_univ_three] at r0 r1 r2 c1 hd ha
  have e0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have e1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have e2 : Fin.rev (2 : Fin 3) = 0 := rfl
  rw [e0, e1, e2] at ha
  linarith

/-- 3×3 の魔方陣の中心は 5。 -/
theorem magic_three_center {M : Fin 3 → Fin 3 → ℤ} (hM : IsMagic 3 M) : M 1 1 = 5 := by
  obtain ⟨_, _, hrow, hcol, hd, ha⟩ := hM
  apply center_three M (fun i => by have := hrow i; norm_num at this; linarith)
    (fun j => by have := hcol j; norm_num at this; linarith)
    (by norm_num at hd; linarith) (by norm_num at ha; linarith)

/-- 洛書。 -/
def loShu : Fin 3 → Fin 3 → ℤ := ![![2, 7, 6], ![9, 5, 1], ![4, 3, 8]]

theorem loShu_isMagic : IsMagic 3 loShu := by decide

/-- (2) 3×3 の中心以外のマスは決まらない。 -/
theorem three_others_not_fixed (i j : Fin 3) (h : (i, j) ≠ (1, 1)) :
    ∃ M M', IsMagic 3 M ∧ IsMagic 3 M' ∧ M i j ≠ M' i j := by
  refine ⟨loShu, compl 3 loShu, loShu_isMagic, complement_isMagic loShu_isMagic, ?_⟩
  revert h
  revert i j
  decide

/-- 原稿の計算 4.2 の 4×4（4A + B + 1）。 -/
def sq4 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 6, 11, 16], ![12, 15, 2, 5], ![14, 9, 8, 3], ![7, 4, 13, 10]]

theorem sq4_isMagic : IsMagic 4 sq4 := by decide

/-- (3) 4×4 ではどのマスも決まらない。 -/
theorem four_not_fixed (i j : Fin 4) : ∃ M', IsMagic 4 M' ∧ M' i j ≠ sq4 i j :=
  even_not_fixed ⟨2, rfl⟩ sq4_isMagic i j

/-- 5×5 の線形の方陣 5((i + 2j) mod 5) + ((2i + j) mod 5) + 1。 -/
def sq5 : Fin 5 → Fin 5 → ℤ :=
  fun i j => 5 * (((i : ℕ) + 2 * j) % 5 : ℕ) + (((2 * i : ℕ) + j) % 5 : ℕ) + 1

/-- 行を一つずらした方陣。 -/
def sq5' : Fin 5 → Fin 5 → ℤ := fun i j => sq5 (i + 1) j

theorem sq5_isMagic : IsMagic 5 sq5 := by decide
theorem sq5'_isMagic : IsMagic 5 sq5' := by decide

theorem sq5_center : sq5 2 2 = 7 := by decide

/-- (3) 5×5 ではどのマスも決まらない（中心も）。 -/
theorem five_not_fixed (i j : Fin 5) :
    ∃ M M', IsMagic 5 M ∧ IsMagic 5 M' ∧ M i j ≠ M' i j := by
  by_cases h : 2 * sq5 i j = 26
  · refine ⟨sq5', compl 5 sq5', sq5'_isMagic, complement_isMagic sq5'_isMagic, ?_⟩
    revert h; revert i j; decide
  · obtain ⟨M', hM', hne⟩ := not_fixed sq5_isMagic (i := i) (j := j) (by norm_num; exact h)
    exact ⟨sq5, M', sq5_isMagic, hM', hne.symm⟩

/-- 原稿の計算 4.3 の 6×6。 -/
def sq6 : Fin 6 → Fin 6 → ℤ :=
  ![![35, 1, 6, 26, 19, 24], ![3, 32, 7, 21, 23, 25], ![31, 9, 2, 22, 27, 20],
    ![8, 28, 33, 17, 10, 15], ![30, 5, 34, 12, 14, 16], ![4, 36, 29, 13, 18, 11]]

theorem sq6_isMagic : IsMagic 6 sq6 := by decide

/-- (3) 6×6 ではどのマスも決まらない。 -/
theorem six_not_fixed (i j : Fin 6) : ∃ M', IsMagic 6 M' ∧ M' i j ≠ sq6 i j :=
  even_not_fixed ⟨3, rfl⟩ sq6_isMagic i j

end Paper638

end Yamagishi
