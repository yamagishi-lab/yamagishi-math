/-
論文1131 の芯：係数の「1/6」の二つの根（1/n! と 1/(2n)）が同じ数になるのは n = 3 だけ。
  (n − 1)! = 2  ⇔  n = 3
  n ≥ 1 のとき  n! = 2n  ⇔  n = 3
2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

/-- 階乗が 2 になるのは、2 のときだけ。 -/
theorem factorial_eq_two_iff (m : ℕ) : Nat.factorial m = 2 ↔ m = 2 := by
  constructor
  · intro h
    rcases m with _ | _ | _ | m
    · simp at h
    · simp at h
    · rfl
    · exfalso
      have h' : Nat.factorial (m + 3) = 2 := h
      have h6 : Nat.factorial 3 ≤ Nat.factorial (m + 3) := Nat.factorial_le (by omega)
      have h3 : Nat.factorial 3 = 6 := by decide
      omega
  · rintro rfl
    decide

/-- 論文1131 の芯：(n − 1)! = 2 となるのは n = 3 だけ。 -/
theorem pred_factorial_eq_two_iff (n : ℕ) : Nat.factorial (n - 1) = 2 ↔ n = 3 := by
  rw [factorial_eq_two_iff]
  omega

/-- 同じことの別の形：n ≥ 1 のとき、n! = 2n となるのは n = 3 だけ（1/n! = 1/(2n) の分母どうし）。 -/
theorem factorial_eq_two_mul_iff (n : ℕ) (hn : 1 ≤ n) : Nat.factorial n = 2 * n ↔ n = 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ]
  constructor
  · intro h
    have hk : Nat.factorial k = 2 := by
      have h' : (k + 1) * Nat.factorial k = (k + 1) * 2 := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) h'
    have := (factorial_eq_two_iff k).mp hk
    omega
  · intro h
    have hk : k = 2 := by omega
    subst hk
    decide

end Yamagishi
