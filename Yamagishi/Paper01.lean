/-
論文01『球対称密度分布における n = 2 の唯一性定理』の芯を、機械に確かめさせる。

原稿（01_uniqueness_n2/uniqueness_theorem_n2_master_jp.tex）の
  補題1：α ∈ ℝ について、f(r) = r^α が (0, ∞) 上で定数 ⇔ α = 0
  定理1：ρ(r) = r^(−n)（n ∈ ℝ）のとき、dm/dr(r) = 4π r^(2−n) が (0, ∞) 上で定数 ⇔ n = 2
を、そのままの形で書く。

形式化したのは数学の中身（実数の冪が定数になる条件）だけである。
「dm/dr は殻一枚の重さの増え方」「ρ は質量密度」という物理の読みは形式化していない。
dm/dr は原稿の定義2どおり 4π r² ρ(r) という式として置き、積分 m(r) の微分としては扱わない
（n ≥ 3 では m(r) = ∫₀ʳ … が発散するため。原稿も dm/dr を式で定義している）。
それとは別に、半径 1 から測った殻の重さ ∫₁ʳ 4π s^(2−n) ds の微分が 4π r^(2−n) であることを
すべての実数 n について示した（`shellMass_from_one_hasDerivAt`）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

open Real

/-- 原稿の定義2：密度 r^(−n) のときの、半径 r での殻一枚あたりの質量の増え方 4π r² ρ(r)。 -/
noncomputable def shellRate (n r : ℝ) : ℝ := 4 * π * r ^ (2 : ℝ) * r ^ (-n)

/-- r > 0 では 4π r² r^(−n) = 4π r^(2−n)（原稿の式(1)の右の等号）。 -/
theorem shellRate_eq (n r : ℝ) (hr : 0 < r) : shellRate n r = 4 * π * r ^ (2 - n) := by
  unfold shellRate
  rw [mul_assoc, ← Real.rpow_add hr, sub_eq_add_neg]

/-- 補題1：実数 α について、r ↦ r^α が (0, ∞) 上で定数（ある C があって、すべての r > 0 で
r^α = C）になるのは α = 0 のときだけ。証明は原稿どおり r = 1 と r = 2 をくらべる。 -/
theorem rpow_const_on_pos_iff (α : ℝ) : (∃ C : ℝ, ∀ r : ℝ, 0 < r → r ^ α = C) ↔ α = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    have h1 : (1 : ℝ) ^ α = C := hC 1 one_pos
    have h2 : (2 : ℝ) ^ α = C := hC 2 two_pos
    rw [Real.one_rpow] at h1
    have h21 : (2 : ℝ) ^ α = 1 := by rw [h2, ← h1]
    have hlog : Real.log ((2 : ℝ) ^ α) = 0 := by rw [h21, Real.log_one]
    rw [Real.log_rpow two_pos] at hlog
    have hl2 : Real.log 2 ≠ 0 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      exact ne_of_gt this
    rcases mul_eq_zero.mp hlog with h | h
    · exact h
    · exact absurd h hl2
  · rintro rfl
    exact ⟨1, fun r _ => Real.rpow_zero r⟩

/-- 定理1（n = 2 の唯一性）：すべての実数 n について、
4π r^(2−n) が (0, ∞) 上で定数関数になるのは n = 2 のときだけ。 -/
theorem uniqueness_n2 (n : ℝ) :
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → 4 * π * r ^ (2 - n) = C) ↔ n = 2 := by
  have h4pi : (4 * π : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨C, hC⟩
    have : ∃ C' : ℝ, ∀ r : ℝ, 0 < r → r ^ (2 - n) = C' :=
      ⟨C / (4 * π), fun r hr => by
        rw [eq_div_iff h4pi, mul_comm]; exact hC r hr⟩
    have h0 := (rpow_const_on_pos_iff (2 - n)).mp this
    linarith
  · rintro rfl
    exact ⟨4 * π, fun r _ => by norm_num⟩

/-- 定理1を、原稿の定義2の式 4π r² ρ(r) のまま書いた形。 -/
theorem uniqueness_n2_shellRate (n : ℝ) :
    (∃ C : ℝ, ∀ r : ℝ, 0 < r → shellRate n r = C) ↔ n = 2 := by
  rw [← uniqueness_n2 n]
  constructor
  · rintro ⟨C, hC⟩; exact ⟨C, fun r hr => by rw [← shellRate_eq n r hr]; exact hC r hr⟩
  · rintro ⟨C, hC⟩; exact ⟨C, fun r hr => by rw [shellRate_eq n r hr]; exact hC r hr⟩

/-- 原稿の定義3は定数を C > 0 と書く。その形でも同じ：一様性条件（正の定数）が成り立つのは
n = 2 のときだけで、そのとき定数は 4π。 -/
theorem uniqueness_n2_pos (n : ℝ) :
    (∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → 4 * π * r ^ (2 - n) = C) ↔ n = 2 := by
  constructor
  · rintro ⟨C, _, hC⟩; exact (uniqueness_n2 n).mp ⟨C, hC⟩
  · rintro rfl
    exact ⟨4 * π, by positivity, fun r _ => by norm_num⟩

/-- n = 2 のとき dm/dr はどの半径でも 4π（原稿の定理1の証明の最後の行）。 -/
theorem shellRate_two (r : ℝ) (hr : 0 < r) : shellRate 2 r = 4 * π := by
  rw [shellRate_eq 2 r hr]; norm_num

/-- 補足：半径 1 から r までの殻の重さ M₁(r) = ∫₁ʳ 4π s^(2−n) ds は、すべての実数 n で、
r > 0 において微分すると 4π r^(2−n) になる（dm/dr という名前の裏づけ）。 -/
theorem shellMass_from_one_hasDerivAt (n r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun R => ∫ s in (1 : ℝ)..R, 4 * π * s ^ (2 - n)) (4 * π * r ^ (2 - n)) r := by
  have hcont : ContinuousOn (fun s : ℝ => 4 * π * s ^ (2 - n)) (Set.Ioi 0) := by
    intro s hs
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const s (2 - n) (Or.inl (ne_of_gt hs)))).continuousWithinAt
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro s hs
    rcases Set.mem_uIcc.mp hs with h | h
    · exact lt_of_lt_of_le one_pos h.1
    · exact lt_of_lt_of_le hr h.1
  · exact hcont.stronglyMeasurableAtFilter isOpen_Ioi r hr
  · exact hcont.continuousAt (Ioi_mem_nhds hr)

end Yamagishi
