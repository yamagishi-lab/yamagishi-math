/-
論文899『線の太さは、幅の端数の割合で画素に丸まる』の格上げ（一般の形）。

原稿（899_yamagishi_stroke_width_rounds_to_pixels_by_its_fraction/…_jp.tex）は、幅 w 画素の縦の線の
左端を位置 φ に置き、画素 k（k から k+1）の中心 k + 0.5 が線の中にあれば黒くするとき、黒い画素の数
（出る太さ）を、幅 0.7・1.3・2.5・2.9 で位置を 10000 通りずらして数え、太いほうになる割合が幅の端数
に等しい（観察 2.2）と数えている。

ここで証明した言明（幅 w > 0 と位置 φ は任意の実数）：
  (1) `count_eq`：黒い画素の数は ⌊w⌋ + [fract(1/2 − φ) < fract w]（[ ] は真なら 1、偽なら 0）。
      `count_cases`：よって数は ⌊w⌋ か ⌊w⌋ + 1 のどちらかで、`count_int`：w が整数なら常に w。
  (2) `prob_thick`：φ を [0, 1) で一様にとると、太いほう（⌊w⌋ + 1 画素）になる位置の集まりの
      長さ（確率）はちょうど fract w。
定義に置いたもの：線を半開区間 [φ, φ + w) とし、黒い画素の数を「φ ≤ k + 1/2 < φ + w を満たす
整数 k の個数」とした（原稿の設定の言い換え）。
差：w が整数のときは太さは一通りで、「二通り」は成り立たない（割合 fract w = 0 で式とは合う）。
形式化していないもの：覆う面積で灰色にしたときの合計が位置によらず w になること。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper899

open MeasureTheory Set

/-- 黒い画素の番号の集まり：φ ≤ k + 1/2 < φ + w。 -/
noncomputable def black (φ w : ℝ) : Finset ℤ := Finset.Ico ⌈φ - 1 / 2⌉ ⌈φ - 1 / 2 + w⌉

theorem mem_black (φ w : ℝ) (k : ℤ) : k ∈ black φ w ↔ φ ≤ k + 1 / 2 ∧ (k : ℝ) + 1 / 2 < φ + w := by
  unfold black
  rw [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- (1) 黒い画素の数 = ⌊w⌋ + [fract(1/2 − φ) < fract w]。 -/
theorem count_eq (φ w : ℝ) (hw : 0 < w) :
    ((black φ w).card : ℤ) = ⌊w⌋ + if Int.fract (1 / 2 - φ) < Int.fract w then 1 else 0 := by
  unfold black
  rw [Int.card_Ico]
  set c := φ - 1 / 2
  set δ := Int.fract (1 / 2 - φ) with hδ
  have hc : (⌈c⌉ : ℝ) = c + δ := by
    have h1 : ⌈c⌉ = -⌊-c⌋ := by rw [Int.floor_neg]; ring
    have h2 : -c = 1 / 2 - φ := by simp only [c]; ring
    rw [h1, h2]
    push_cast
    rw [hδ, Int.fract]
    simp only [c]; ring
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  -- ⌈c + w⌉ − ⌈c⌉ = ⌈w − δ⌉
  have hdiff : ⌈c + w⌉ - ⌈c⌉ = ⌈w - δ⌉ := by
    have : c + w = (w - δ) + (⌈c⌉ : ℝ) := by rw [hc]; ring
    rw [this, Int.ceil_add_intCast]; ring
  set f := Int.fract w with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  have hwf : w = ⌊w⌋ + f := by rw [hf, Int.floor_add_fract]
  have hceil : ⌈w - δ⌉ = ⌊w⌋ + if δ < f then 1 else 0 := by
    have : w - δ = (f - δ) + (⌊w⌋ : ℝ) := by linarith [hwf]
    rw [this, Int.ceil_add_intCast]
    split_ifs with h
    · have : ⌈f - δ⌉ = 1 := by
        rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
      rw [this]; ring
    · have : ⌈f - δ⌉ = 0 := by
        rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
      rw [this]; ring
  have hnn : 0 ≤ ⌈c + w⌉ - ⌈c⌉ := by
    rw [hdiff, hceil]
    have : 0 ≤ ⌊w⌋ := Int.floor_nonneg.mpr hw.le
    split_ifs <;> omega
  rw [Int.toNat_of_nonneg hnn, hdiff, hceil]

/-- 数は ⌊w⌋ か ⌊w⌋ + 1 のどちらか。 -/
theorem count_cases (φ w : ℝ) (hw : 0 < w) :
    ((black φ w).card : ℤ) = ⌊w⌋ ∨ ((black φ w).card : ℤ) = ⌊w⌋ + 1 := by
  rw [count_eq φ w hw]
  split_ifs <;> simp

/-- w が整数なら、どの位置でも数は w。 -/
theorem count_int (φ : ℝ) (n : ℕ) (hn : 0 < n) : (black φ n).card = n := by
  have := count_eq φ n (by exact_mod_cast hn)
  rw [Int.fract_natCast, Int.floor_natCast] at this
  have h : ¬ Int.fract (1 / 2 - φ) < 0 := not_lt.mpr (Int.fract_nonneg _)
  rw [ite_eq_right_of_eq_false _ _ (eq_false h), add_zero] at this
  exact_mod_cast this

/-- [0, 1) の上で fract(1/2 − φ) の形。 -/
theorem fract_half_sub {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < 1) :
    Int.fract (1 / 2 - φ) = if φ ≤ 1 / 2 then 1 / 2 - φ else 3 / 2 - φ := by
  split_ifs with h
  · rw [Int.fract_eq_self]; constructor <;> linarith
  · rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩

/-- (2) φ を [0, 1) で一様にとると、太いほうになる位置の集まりの長さはちょうど fract w。 -/
theorem prob_thick (w : ℝ) :
    volume {φ ∈ Ico (0 : ℝ) 1 | Int.fract (1 / 2 - φ) < Int.fract w} =
      ENNReal.ofReal (Int.fract w) := by
  set f := Int.fract w with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  by_cases hhalf : f ≤ 1 / 2
  · have : {φ ∈ Ico (0 : ℝ) 1 | Int.fract (1 / 2 - φ) < f} = Ioc (1 / 2 - f) (1 / 2) := by
      ext φ
      simp only [mem_Ico, mem_Ioc]
      constructor
      · rintro ⟨⟨h0, h1⟩, h⟩
        rw [fract_half_sub h0 h1] at h
        split_ifs at h with hφ
        · constructor <;> linarith
        · exfalso; linarith
      · rintro ⟨h1, h2⟩
        have h0 : 0 ≤ φ := by linarith
        refine ⟨⟨h0, by linarith⟩, ?_⟩
        rw [fract_half_sub h0 (by linarith), ite_eq_left_of_eq_true _ _ (eq_true h2)]; linarith
    rw [this, Real.volume_Ioc]; congr 1; ring
  · push Not at hhalf
    have : {φ ∈ Ico (0 : ℝ) 1 | Int.fract (1 / 2 - φ) < f} =
        Icc 0 (1 / 2) ∪ Ioo (3 / 2 - f) 1 := by
      ext φ
      simp only [mem_Ico, mem_union, mem_Icc, mem_Ioo]
      constructor
      · rintro ⟨⟨h0, h1⟩, h⟩
        rw [fract_half_sub h0 h1] at h
        split_ifs at h with hφ
        · left; exact ⟨h0, hφ⟩
        · right; constructor <;> linarith
      · rintro (⟨h0, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨⟨h0, by linarith⟩, ?_⟩
          rw [fract_half_sub h0 (by linarith), ite_eq_left_of_eq_true _ _ (eq_true h2)]; linarith
        · have h0 : 0 ≤ φ := by linarith
          refine ⟨⟨h0, h2⟩, ?_⟩
          rw [fract_half_sub h0 h2, ite_eq_right_of_eq_false _ _ (eq_false (by linarith))]; linarith
    rw [this, measure_union _ measurableSet_Ioo, Real.volume_Icc, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    · congr 1; ring
    · rw [Set.disjoint_left]
      rintro φ ⟨_, h2⟩ ⟨h3, _⟩
      linarith

end Paper899

end Yamagishi
