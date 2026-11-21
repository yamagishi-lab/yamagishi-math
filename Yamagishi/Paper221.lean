/-
論文221『最後の桁を一つ変えると、固有値が 0.16 動く』の格上げ（一般の形）。

原稿（221_yamagishi_last_bit_moves_an_eigenvalue/…_jp.tex）は、固有値 0 の n×n のジョルダン細胞の
左下の隅に ε を置いた行列について、n = 2, 4, 8, 10, 16, 20 の数値で固有値の大きさの比
1.0000000000 を、n = 12 で角の間隔 2π/12 を測っている。特性多項式は書いていない。

ここで証明した言明（n = m + 1 ≥ 1、ε は体 K の任意の元。行列 A は (i, i + 1) 成分が 1、
(n − 1, 0) 成分が ε、ほかは 0）：
  (1) `eigen_iff`：λ が A の固有値（零でない v で Av = λv）⇔ λⁿ = ε。固有ベクトルは (1, λ, …, λⁿ⁻¹)。
  (2) `eigen_abs`（K = ℂ）：固有値の絶対値はどれも |ε|^(1/n)（半径 |ε|^(1/n) の円周の上）。
  (3) `eigen_rotate`（K = ℂ）：λ が固有値なら、1 の n 乗根 ζ を掛けた ζλ も固有値（固有値の集まりは
      角 2π/n の回転で動かない。ε ≠ 0 なら等間隔に並ぶ n 個の点）。
  (4) `eigen_zero_iff`：ε = 0 なら固有値は 0 だけ（もとのジョルダン細胞）。
形式化していないもの：特性多項式が λⁿ − ε であること（固有値の集まりとして述べた）、
擬スペクトルの半径が ε^(1/n) に漸近的に一致すること、数値の比。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper221

open Matrix

variable {K : Type*} [Field K]

/-- 隅に ε を置いたジョルダン細胞（大きさ m + 1）。 -/
def A (m : ℕ) (ε : K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if (j : ℕ) = i + 1 then 1 else if (i : ℕ) = m ∧ (j : ℕ) = 0 then ε else 0

theorem mulVec_lt {m : ℕ} (ε : K) (v : Fin (m + 1) → K) (i : Fin (m + 1)) (hi : (i : ℕ) < m) :
    (A m ε *ᵥ v) i = v ⟨i + 1, by omega⟩ := by
  simp only [mulVec, dotProduct, A]
  rw [Finset.sum_eq_single ⟨i + 1, by omega⟩]
  · simp
  · intro j _ hj
    have h1 : ¬ (j : ℕ) = i + 1 := fun h => hj (Fin.ext h)
    have h2 : ¬ ((i : ℕ) = m ∧ (j : ℕ) = 0) := fun h => by omega
    simp only [h1, h2, ite_false, zero_mul]
  · simp

theorem mulVec_last {m : ℕ} (ε : K) (v : Fin (m + 1) → K) :
    (A m ε *ᵥ v) (Fin.last m) = ε * v 0 := by
  simp only [mulVec, dotProduct, A]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    have h1 : ¬ (j : ℕ) = (Fin.last m : ℕ) + 1 := by have := j.isLt; simp; omega
    have h2 : ¬ (((Fin.last m : Fin (m + 1)) : ℕ) = m ∧ (j : ℕ) = 0) := by
      rintro ⟨-, h⟩; exact hj (Fin.ext h)
    simp only [h1, h2, ite_false, zero_mul]
  · simp

/-- (1) 固有値 ⇔ λⁿ = ε。 -/
theorem eigen_iff {m : ℕ} (ε lam : K) :
    (∃ v : Fin (m + 1) → K, v ≠ 0 ∧ A m ε *ᵥ v = lam • v) ↔ lam ^ (m + 1) = ε := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    -- v i = λ^i v 0
    have hstep : ∀ i : ℕ, ∀ hi : i < m, v ⟨i + 1, by omega⟩ = lam * v ⟨i, by omega⟩ := by
      intro i hi
      have := congrFun hAv ⟨i, by omega⟩
      rw [mulVec_lt ε v ⟨i, by omega⟩ hi] at this
      simpa using this
    have hpow : ∀ i : ℕ, ∀ hi : i < m + 1, v ⟨i, hi⟩ = lam ^ i * v 0 := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ k ih =>
        intro hi
        rw [hstep k (by omega), ih (by omega), pow_succ]; ring
    have hlast := congrFun hAv (Fin.last m)
    rw [mulVec_last] at hlast
    simp only [Pi.smul_apply, smul_eq_mul] at hlast
    have hm : v (Fin.last m) = lam ^ m * v 0 := hpow m (by omega)
    rw [hm] at hlast
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      funext i
      rw [show i = ⟨i, i.isLt⟩ from rfl, hpow i i.isLt, h0, mul_zero]
      rfl
    have : (lam ^ (m + 1) - ε) * v 0 = 0 := by rw [pow_succ]; linear_combination -hlast
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv0)
  · intro h
    refine ⟨fun i => lam ^ (i : ℕ), ?_, ?_⟩
    · intro h0
      have := congrFun h0 0
      simp at this
    · funext i
      by_cases hi : (i : ℕ) < m
      · rw [mulVec_lt ε _ i hi]
        simp [pow_succ, mul_comm]
      · have hil : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
        rw [hil, mulVec_last]
        simp [← h, pow_succ, mul_comm]

/-- (4) ε = 0 なら固有値は 0 だけ。 -/
theorem eigen_zero_iff {m : ℕ} (lam : K) :
    (∃ v : Fin (m + 1) → K, v ≠ 0 ∧ A m 0 *ᵥ v = lam • v) ↔ lam = 0 := by
  rw [eigen_iff]; exact pow_eq_zero_iff (by omega)

/-- (2) 複素数では、固有値の絶対値は |ε|^(1/n)。 -/
theorem eigen_abs {m : ℕ} {ε lam : ℂ} (h : ∃ v : Fin (m + 1) → ℂ, v ≠ 0 ∧ A m ε *ᵥ v = lam • v) :
    ‖lam‖ = ‖ε‖ ^ (1 / ((m : ℝ) + 1)) := by
  rw [eigen_iff] at h
  have h1 : ‖lam‖ ^ (m + 1) = ‖ε‖ := by rw [← norm_pow, h]
  rw [← h1, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have : ((m + 1 : ℕ) : ℝ) * (1 / ((m : ℝ) + 1)) = 1 := by push_cast; field_simp
  rw [this, Real.rpow_one]

/-- (3) 固有値の集まりは、1 の n 乗根を掛けても動かない。 -/
theorem eigen_rotate {m : ℕ} {ε lam ζ : ℂ} (hζ : ζ ^ (m + 1) = 1)
    (h : ∃ v : Fin (m + 1) → ℂ, v ≠ 0 ∧ A m ε *ᵥ v = lam • v) :
    ∃ v : Fin (m + 1) → ℂ, v ≠ 0 ∧ A m ε *ᵥ v = (ζ * lam) • v := by
  rw [eigen_iff] at h ⊢
  rw [mul_pow, hζ, one_mul, h]

end Paper221

end Yamagishi
