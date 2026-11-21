/-
論文992『自分の出る時刻が早いほうの出口を選ぶと、最良の境と一致する』の格上げ（一般の形）。

原稿（992_yamagishi_picking_ones_own_fastest_exit_matches_the_best_boundary/…_jp.tex）は、両端に出口
A・B のある通路で、A に近い順に 1〜N と番号をつけた人が、境 j で 1〜j は A、j+1〜N は B に向かう
とき、境の両側の人がどちらも乗り換えたくない「釣り合い」を、180 の並び（人数 60・200・600、
幅の比 1・2・3、並び 20 通り）で全部の境から探し、どれでも釣り合いはちょうど一つで、最後の人の時間
を最も短くする境とも、平均を最も短くする境とも一致した、と数えている（観察 4.2 で「境の人は列の最後
に並び、ほかの人の時刻を変えない」と述べる）。

ここで証明した言明（人数 N、A・B に着く時刻 tA i・tB i は任意の実数、出口の間隔 sA・sB > 0）：
  A の列の出る時刻 DA(i) = max(tA i, DA(i−1)) + sA（DA(0) = 0）、
  B の列の出る時刻 EB(i) = max(tB i, EB(i+1)) + sB（i ≤ N、EB(N+1) = 0）と置く。
  境 j の釣り合い：j 番目が B に移っても早くならない（DA j ≤ EB j）、j+1 番目が A に移っても早く
  ならない（EB(j+1) ≤ DA(j+1)）。
  (1) `DA_strictMono`・`EB_lt`：DA は狭義に増え、EB は狭義に減る。
  (2) `eq_exists`：釣り合いはどの並びでも在る。
  (3) `eq_unique`：二つあれば隣どうしで、その境の人がちょうど同着（DA k = EB k）。
      同着が無ければ釣り合いは一つ。
  (4) `sum_le_of_eq`：釣り合いの境は、全員の出る時刻の和を最小にする。
  (5) `makespan_le_of_eq`：釣り合いの境は、最後の人の時刻（最大）を最小にする。
      `makespan_spec`：境 j の最後の人の時刻は max(DA j, EB(j+1)) で、だれかの時刻に等しい。
模型として置いたもの：A の列は番号の順、B の列は番号の逆順に出る（各人の位置が A に近い順に並び、
全員が同じ速さで歩けば、着く順はこの順になるので、先入れ先出しの列と同じ。追い越しや人ごとに違う
速さは扱わない）。列は時刻 0 で空。着く時刻の値には仮定を置かない。
証明の要（観察 4.2 そのもの）：境を一人ずらして変わるのは境の人自身の時刻だけで、
和の差は h(j) = DA j − EB j。h は狭義に増えるので、和は離散的に凸で、最小は h の符号が変わる所。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper992

open Finset

variable (N : ℕ) (tA tB : ℕ → ℝ) (sA sB : ℝ)

/-- A の列の出る時刻（1 番目から順に）。 -/
def DA : ℕ → ℝ
  | 0 => 0
  | i + 1 => max (tA (i + 1)) (DA i) + sA

/-- B の列の出る時刻（N 番目から逆順に）。 -/
def EB (i : ℕ) : ℝ := if N < i then 0 else max (tB i) (EB (i + 1)) + sB
termination_by N + 1 - i

variable {N tA tB sA sB}

theorem EB_of_le {i : ℕ} (h : i ≤ N) : EB N tB sB i = max (tB i) (EB N tB sB (i + 1)) + sB := by
  rw [EB]; simp [show ¬ N < i by omega]

theorem EB_of_gt {i : ℕ} (h : N < i) : EB N tB sB i = 0 := by
  rw [EB]; simp [h]

/-- (1) DA は狭義に増える。 -/
theorem DA_succ_gt (hA : 0 < sA) (i : ℕ) : DA tA sA i < DA tA sA (i + 1) := by
  show DA tA sA i < max (tA (i + 1)) (DA tA sA i) + sA
  linarith [le_max_right (tA (i + 1)) (DA tA sA i)]

theorem DA_strictMono (hA : 0 < sA) : StrictMono (DA tA sA) :=
  strictMono_nat_of_lt_succ (DA_succ_gt hA)

theorem DA_nonneg (hA : 0 < sA) (i : ℕ) : 0 ≤ DA tA sA i := by
  have := (DA_strictMono (tA := tA) hA).monotone (Nat.zero_le i)
  simpa [DA] using this

/-- (1) EB は狭義に減る（i ≤ N で EB(i+1) < EB i）。 -/
theorem EB_succ_lt (hB : 0 < sB) {i : ℕ} (h : i ≤ N) : EB N tB sB (i + 1) < EB N tB sB i := by
  rw [EB_of_le h (tB := tB)]
  linarith [le_max_right (tB i) (EB N tB sB (i + 1))]

theorem EB_lt (hB : 0 < sB) {i k : ℕ} (hik : i < k) (hk : k ≤ N + 1) :
    EB N tB sB k < EB N tB sB i := by
  induction k, hik using Nat.le_induction with
  | base => exact EB_succ_lt hB (by omega)
  | succ k hk' ih => exact (EB_succ_lt hB (by omega)).trans (ih (by omega))

theorem EB_le (hB : 0 < sB) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ N + 1) :
    EB N tB sB k ≤ EB N tB sB i := by
  rcases eq_or_lt_of_le hik with rfl | h
  · exact le_rfl
  · exact (EB_lt hB h hk).le

theorem EB_nonneg (hB : 0 < sB) (i : ℕ) : 0 ≤ EB N tB sB i := by
  by_cases h : N < i
  · rw [EB_of_gt h]
  · have := EB_le (N := N) (tB := tB) hB (show i ≤ N + 1 by omega) le_rfl
    rw [EB_of_gt (show N < N + 1 by omega)] at this
    exact this

/-! ## 釣り合い -/

/-- 境 j（0 ≤ j ≤ N）の釣り合い：両側の人がどちらも乗り換えて早くならない。 -/
def IsEq (N : ℕ) (tA tB : ℕ → ℝ) (sA sB : ℝ) (j : ℕ) : Prop :=
  (1 ≤ j → DA tA sA j ≤ EB N tB sB j) ∧ (j + 1 ≤ N → EB N tB sB (j + 1) ≤ DA tA sA (j + 1))

/-- 乗り換えた人の時刻：j 番目が B に移ると時刻は EB j、j+1 番目が A に移ると DA(j+1)。
（定義から直ちに：EB j = max(tB j, EB(j+1)) + sB、DA(j+1) = max(tA(j+1), DA j) + sA。） -/
theorem switch_times (j : ℕ) (hj : j ≤ N) :
    EB N tB sB j = max (tB j) (EB N tB sB (j + 1)) + sB ∧
    DA tA sA (j + 1) = max (tA (j + 1)) (DA tA sA j) + sA :=
  ⟨EB_of_le hj, rfl⟩

/-- (2) 釣り合いはどの並びでも在る。 -/
theorem eq_exists : ∃ j, j ≤ N ∧ IsEq N tA tB sA sB j := by
  classical
  have hex : ∃ j, N ≤ j ∨ EB N tB sB (j + 1) ≤ DA tA sA (j + 1) := ⟨N, Or.inl le_rfl⟩
  let j := Nat.find hex
  have hj : N ≤ j ∨ EB N tB sB (j + 1) ≤ DA tA sA (j + 1) := Nat.find_spec hex
  have hjN : j ≤ N := Nat.find_min' hex (Or.inl le_rfl)
  refine ⟨j, hjN, ?_, ?_⟩
  · intro h1
    have hmin := Nat.find_min hex (show j - 1 < j by omega)
    push Not at hmin
    have e : j - 1 + 1 = j := by omega
    rw [e] at hmin
    exact hmin.2.le
  · intro h2
    rcases hj with h | h
    · omega
    · exact h

/-- (3) 釣り合いが二つあれば、隣どうしで、その境の人はちょうど同着。 -/
theorem eq_unique (hA : 0 < sA) (hB : 0 < sB) {j k : ℕ} (hjk : j < k) (hk : k ≤ N)
    (hj : IsEq N tA tB sA sB j) (hk' : IsEq N tA tB sA sB k) :
    k = j + 1 ∧ DA tA sA k = EB N tB sB k := by
  have h1 := hj.2 (by omega)
  have h2 := hk'.1 (by omega)
  by_contra hne
  have : j + 1 < k ∨ (k = j + 1 ∧ DA tA sA k ≠ EB N tB sB k) := by
    by_cases e : k = j + 1
    · right; exact ⟨e, fun h => hne ⟨e, h⟩⟩
    · left; omega
  rcases this with hlt | ⟨rfl, hne'⟩
  · have a1 := DA_strictMono (tA := tA) hA hlt
    have a2 := EB_lt (N := N) (tB := tB) hB hlt (by omega)
    linarith
  · exact hne' (le_antisymm h2 h1)

/-- 同着が無ければ釣り合いはただ一つ。 -/
theorem eq_unique_of_no_tie (hA : 0 < sA) (hB : 0 < sB)
    (hnt : ∀ i, 1 ≤ i → i ≤ N → DA tA sA i ≠ EB N tB sB i) {j k : ℕ} (hjN : j ≤ N) (hkN : k ≤ N)
    (hj : IsEq N tA tB sA sB j) (hk : IsEq N tA tB sA sB k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd (eq_unique hA hB h hkN hj hk).2 (hnt k (by omega) hkN)
  · exact h
  · exact absurd (eq_unique hA hB h hjN hk hj).2 (hnt j (by omega) hjN)

/-! ## 和の最小 -/

/-- 境 j での全員の出る時刻の和。 -/
noncomputable def S (N : ℕ) (tA tB : ℕ → ℝ) (sA sB : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 j, DA tA sA i + ∑ i ∈ Icc (j + 1) N, EB N tB sB i

/-- 境を一人ずらすと、和は境の人の時刻の差 h = DA − EB だけ変わる。 -/
theorem S_succ (j : ℕ) (hj : j + 1 ≤ N) :
    S N tA tB sA sB (j + 1) = S N tA tB sA sB j + (DA tA sA (j + 1) - EB N tB sB (j + 1)) := by
  unfold S
  rw [Finset.sum_Icc_succ_top (by omega)]
  have : Icc (j + 1) N = insert (j + 1) (Icc (j + 1 + 1) N) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring

/-- (4) 釣り合いの境は、全員の出る時刻の和を最小にする。 -/
theorem sum_le_of_eq (hA : 0 < sA) (hB : 0 < sB) {j : ℕ} (hjN : j ≤ N)
    (hj : IsEq N tA tB sA sB j) {k : ℕ} (hk : k ≤ N) :
    S N tA tB sA sB j ≤ S N tA tB sA sB k := by
  rcases le_total j k with hjk | hkj
  · -- 右へずらすと、h(i) ≥ h(j+1) ≥ 0 の分だけ増える
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih =>
      rw [S_succ k hk]
      have := ih (by omega)
      have h0 := hj.2 (by omega)
      have a1 := (DA_strictMono (tA := tA) hA).monotone (show j + 1 ≤ k + 1 by omega)
      have a2 := EB_le (N := N) (tB := tB) hB (show j + 1 ≤ k + 1 by omega) (by omega)
      linarith
  · -- 左から j へ寄せると、h(m+1) ≤ h(j) ≤ 0 の分だけ減る
    have key : ∀ m, k ≤ m → m ≤ j → S N tA tB sA sB m ≤ S N tA tB sA sB k := by
      intro m hkm
      induction m, hkm using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ m hkm ih =>
        intro hmj
        rw [S_succ m (by omega)]
        have := ih (by omega)
        have h0 := hj.1 (by omega)
        have a1 := (DA_strictMono (tA := tA) hA).monotone (show m + 1 ≤ j by omega)
        have a2 := EB_le (N := N) (tB := tB) hB (show m + 1 ≤ j by omega) (by omega)
        linarith
    exact key j hkj le_rfl

/-! ## 最後の人の時刻の最小 -/

/-- 境 j での最後の人の時刻。 -/
noncomputable def M (N : ℕ) (tA tB : ℕ → ℝ) (sA sB : ℝ) (j : ℕ) : ℝ :=
  max (DA tA sA j) (EB N tB sB (j + 1))

/-- 境 j で i 番目の人の出る時刻。 -/
noncomputable def T (N : ℕ) (tA tB : ℕ → ℝ) (sA sB : ℝ) (j i : ℕ) : ℝ :=
  if i ≤ j then DA tA sA i else EB N tB sB i

/-- M j は全員の時刻の上界で、（人が一人以上いれば）だれかの時刻に等しい。 -/
theorem makespan_spec (hA : 0 < sA) (hB : 0 < sB) {j : ℕ} (hjN : j ≤ N) :
    (∀ i, 1 ≤ i → i ≤ N → T N tA tB sA sB j i ≤ M N tA tB sA sB j) ∧
    (1 ≤ N → ∃ i, 1 ≤ i ∧ i ≤ N ∧ T N tA tB sA sB j i = M N tA tB sA sB j) := by
  refine ⟨fun i _ hiN => ?_, fun hN => ?_⟩
  · unfold T M
    split_ifs with hij
    · exact le_max_of_le_left ((DA_strictMono (tA := tA) hA).monotone hij)
    · exact le_max_of_le_right (EB_le (N := N) (tB := tB) hB (by omega) (by omega))
  · unfold T M
    rcases le_total (DA tA sA j) (EB N tB sB (j + 1)) with h | h
    · rw [max_eq_right h]
      by_cases hj1 : j + 1 ≤ N
      · exact ⟨j + 1, by omega, hj1, by simp⟩
      · have hjN' : j = N := by omega
        subst hjN'
        rw [EB_of_gt (show j < j + 1 by omega)] at h ⊢
        have := DA_strictMono (tA := tA) hA (show 0 < j by omega)
        simp [DA] at this
        linarith
    · rw [max_eq_left h]
      by_cases hj0 : 1 ≤ j
      · exact ⟨j, hj0, hjN, by simp⟩
      · have : j = 0 := by omega
        subst this
        have := EB_succ_lt (tB := tB) (N := N) hB (show 1 ≤ N from hN)
        have := EB_nonneg (N := N) (tB := tB) hB (1 + 1)
        simp [DA] at h
        linarith

/-- (5) 釣り合いの境は、最後の人の時刻を最小にする。 -/
theorem makespan_le_of_eq (hA : 0 < sA) (hB : 0 < sB) {j : ℕ} (hjN : j ≤ N)
    (hj : IsEq N tA tB sA sB j) {k : ℕ} (hk : k ≤ N) :
    M N tA tB sA sB j ≤ M N tA tB sA sB k := by
  unfold M
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · -- 右：M k ≥ DA k ≥ DA(j+1) ≥ EB(j+1)、DA k ≥ DA j
    have a1 := (DA_strictMono (tA := tA) hA).monotone (show j + 1 ≤ k by omega)
    have a2 := (DA_strictMono (tA := tA) hA).monotone (show j ≤ k by omega)
    have h0 := hj.2 (by omega)
    exact max_le (le_max_of_le_left a2) (le_max_of_le_left (h0.trans a1))
  · exact le_rfl
  · -- 左：M k ≥ EB(k+1) ≥ EB j ≥ DA j、EB(k+1) ≥ EB(j+1)
    have a1 := EB_le (N := N) (tB := tB) hB (show k + 1 ≤ j by omega) (by omega)
    have a2 := EB_le (N := N) (tB := tB) hB (show k + 1 ≤ j + 1 by omega) (by omega)
    have h0 := hj.1 (by omega)
    exact max_le (le_max_of_le_right (h0.trans a1)) (le_max_of_le_right a2)

end Paper992

end Yamagishi
