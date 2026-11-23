/-
論文635『無作為に止める車は道の 0.747598 で詰まり、二マスずつ占めれば 0.864665 まで入る』の芯
（原稿の漸化式から k = 1・2 の埋まる割合。1/k の漸近は止めた）。

日本語：n マスの列に k マスの車を無作為に止める原稿の漸化式から、埋まる割合 kE(n)/n は、
k = 1 で 1、k = 2 で 1 − e⁻² に近づくことを機械で確かめた。
English: From the paper's recursion for random sequential parking of k-cell cars on n cells, the
filled fraction kE(n)/n tends to 1 for k = 1 and to 1 − e⁻² for k = 2.

原稿（635_yamagishi_cars_parked_at_random_jam_at_0_747598_of_the_street/…_jp.tex）は、漸化式
E(n) = 1 + (2/(n − k + 1))Σ_{i=0}^{n−k} E(i)（n ≥ k）、E(n) = 0（n < k）を数値で解き、k = 1・2・3・5・10・
100・1000 の埋まる割合と、レーニの定数 0.747598 との差に k を掛けた値（k = 100 で 0.216543、
k = 1000 で 0.216217）を示す。「差はおよそ 0.2165/k」と書き、式は示さないと明記している。

ここで証明した言明（漸化式は原稿のものを定義に置いた）：
  (1) `E_rec`・`E_lt`：k ≥ 1 で、定義した E は原稿の漸化式を満たす。
  (2) `E_one`：k = 1 では E(n) = n。`fraction_one`：埋まる割合は 1（いつでも全部埋まる）。
  (3) `E_two_diff`：k = 2 では E(n + 1) − E(n) = Σ_{j<n} (−2)^j/(j + 1)!。
      `fraction_two`：2E(n)/n → 1 − e⁻²（原稿の 0.864665、フローリーの値）。
止めた所：下読みの AI の定理の案「k → ∞ で θ_k = c_R + (c_R − e^(−2γ))/(2k) + O(1/k²)」（c_R はレーニの定数、
γ はオイラーの定数）。θ_k の積分の式を漸化式から出す所（母関数）、内側のオイラー＝マクローリンと
外側の評価の接ぎ合わせは、ここでは形式化していない。k について単調に下がることも扱っていない。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper635

open Finset Filter Topology

/-! ### (1) 原稿の漸化式 -/

/-- n マスの列に k マスの車を止めたときの台数の期待値 E_k(n)（原稿の漸化式）。
和の中の条件 i < n は、k ≥ 1 ならいつも成り立つ（再帰の停止のために置いた）。 -/
noncomputable def E (k : ℕ) : ℕ → ℝ
  | n => if n < k then 0 else
      1 + 2 / ((n - k + 1 : ℕ) : ℝ) *
        ∑ i : Fin (n - k + 1), if _h : (i : ℕ) < n then E k i else 0

theorem E_lt {k n : ℕ} (hn : n < k) : E k n = 0 := by
  rw [E]; simp [hn]

/-- (1) k ≥ 1、n ≥ k で E(n) = 1 + (2/(n − k + 1)) Σ_{i=0}^{n−k} E(i)。 -/
theorem E_rec {k n : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) :
    E k n = 1 + 2 / ((n - k + 1 : ℕ) : ℝ) * ∑ i ∈ range (n - k + 1), E k i := by
  rw [E]
  dsimp only
  split_ifs with h0
  · omega
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun i => if _h : i < n then E k i else 0)]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  split_ifs with h1
  · rfl
  · omega

/-! ### (2) k = 1 -/

theorem E_one (n : ℕ) : E 1 n = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [E_lt (by norm_num)]; simp
    · rw [E_rec le_rfl h]
      have e : ∑ i ∈ range (n - 1 + 1), E 1 i = ∑ i ∈ range n, (i : ℝ) := by
        rw [show n - 1 + 1 = n by omega]
        apply sum_congr rfl
        intro i hi
        exact ih i (mem_range.mp hi)
      rw [e, show n - 1 + 1 = n by omega]
      have hs : (∑ i ∈ range n, (i : ℝ)) * 2 = n * (n - 1) := by
        have h' : ((∑ i ∈ range n, i : ℕ) : ℝ) * 2 = ((n * (n - 1) : ℕ) : ℝ) := by
          exact_mod_cast sum_range_id_mul_two n
        rw [Nat.cast_sum] at h'
        push_cast [Nat.cast_sub h] at h'
        exact h'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      field_simp
      linarith

/-- (2) k = 1 で埋まる割合 E(n)/n → 1。 -/
theorem fraction_one : Tendsto (fun n : ℕ => 1 * E 1 n / n) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [E_one]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-! ### (3) k = 2 -/

/-- c_j = (−2)^j/(j + 1)!。 -/
noncomputable def c (j : ℕ) : ℝ := (-2) ^ j / ((j + 1).factorial : ℝ)

/-- P(n) = Σ_{j<n} c_j。 -/
noncomputable def P (n : ℕ) : ℝ := ∑ j ∈ range n, c j

/-- F(n) = Σ_{i<n} P(i)。 -/
noncomputable def F (n : ℕ) : ℝ := ∑ i ∈ range n, P i

theorem c_succ (j : ℕ) : ((j : ℝ) + 2) * c (j + 1) = -2 * c j := by
  unfold c
  rw [Nat.factorial_succ (j + 1)]
  push_cast
  have : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem F_iii (m : ℕ) : F m = P m + ((m : ℝ) + 1) * P (m + 1) - 1 := by
  induction m with
  | zero => simp [F, P, c]
  | succ m ih =>
    have h1 : F (m + 1) = F m + P m := by unfold F; rw [sum_range_succ]
    have h2 : P (m + 1) = P m + c m := by unfold P; rw [sum_range_succ]
    have h3 : P (m + 2) = P m + c m + c (m + 1) := by
      unfold P; rw [sum_range_succ, sum_range_succ]
    have h4 := c_succ m
    rw [h1, ih]
    push_cast
    rw [h3, h2]
    linear_combination -h4

theorem F_sumform (m : ℕ) :
    ((m : ℝ) + 1) * F (m + 2) = ((m : ℝ) + 1) + 2 * ∑ i ∈ range (m + 1), F i := by
  induction m with
  | zero => simp [F, P, c, sum_range_succ]
  | succ m ih =>
    have h1 : F (m + 3) = F (m + 2) + P (m + 2) := by unfold F; rw [sum_range_succ]
    have h2 : F (m + 2) = F (m + 1) + P (m + 1) := by unfold F; rw [sum_range_succ]
    have h3 : F (m + 1) = P (m + 1) + ((m : ℝ) + 2) * P (m + 2) - 1 := by
      have := F_iii (m + 1)
      push_cast at this
      simp only [show m + 1 + 1 = m + 2 from rfl] at this
      linear_combination this
    rw [sum_range_succ]
    push_cast
    simp only [show m + 1 + 2 = m + 3 from rfl]
    rw [h1]
    linear_combination ih + h2 - h3

/-- E₂(n) = F(n)。 -/
theorem E_two (n : ℕ) : E 2 n = F n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 2 with h | h
    · rw [E_lt h]
      interval_cases n <;> simp [F, P]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [E_rec (by norm_num) h, show m + 2 - 2 + 1 = m + 1 by omega]
      have e : ∑ i ∈ range (m + 1), E 2 i = ∑ i ∈ range (m + 1), F i := by
        apply sum_congr rfl
        intro i hi
        exact ih i (by rw [mem_range] at hi; omega)
      rw [e]
      have hs := F_sumform m
      have hm : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hm]
      have : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      linarith

/-- (3) E₂(n + 1) − E₂(n) = Σ_{j<n} (−2)^j/(j + 1)!。 -/
theorem E_two_diff (n : ℕ) :
    E 2 (n + 1) - E 2 n = ∑ j ∈ range n, (-2 : ℝ) ^ j / ((j + 1).factorial : ℝ) := by
  rw [E_two, E_two]
  unfold F
  rw [sum_range_succ]
  simp [P, c]

/-- Σ c_j = (1 − e⁻²)/2。 -/
theorem hasSum_c : HasSum c ((1 - Real.exp (-2)) / 2) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-2 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  have h2 := h1.mul_left (-(1 / 2 : ℝ))
  convert h2 using 1
  · funext j
    unfold c
    rw [Nat.factorial_succ]
    push_cast
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · simp
    ring

/-- (3) k = 2 で埋まる割合 2E(n)/n → 1 − e⁻²。 -/
theorem fraction_two : Tendsto (fun n : ℕ => 2 * E 2 n / n) atTop (𝓝 (1 - Real.exp (-2))) := by
  have hP : Tendsto P atTop (𝓝 ((1 - Real.exp (-2)) / 2)) := hasSum_c.tendsto_sum_nat
  have hC := hP.cesaro
  have := hC.const_mul 2
  rw [show 2 * ((1 - Real.exp (-2)) / 2) = 1 - Real.exp (-2) by ring] at this
  apply this.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [E_two]
  unfold F
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Paper635

end Yamagishi
