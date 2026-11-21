/-
論文1008『体積の積は束を見分けず、ミルナーの球面は k²−1 の 7 の余りで分かれる』の格上げ（一般の形）。

原稿（1008_yamagishi_volume_products_miss_bundles_and_milnor_spheres_split_by_k2_minus_1_mod_7/
…_jp.tex）は、(i) 球面の体積の積 Vol(S^(2n−1)) = Vol(S^(n−1))·Vol(S^n_(1/2)) を n = 1〜12 の数値で、
(ii) ラドン＝フルヴィッツ数 ρ(n) = n となる n が 1〜64 で 1・2・4・8 だけであることを数え上げで、
(iii) ミルナーの不変量 λ ≡ 2(2k)²−1 (mod 7) が k²−1 の 7 の余りに等しいことを奇数 k = −49〜49 で
確かめている。

ここで証明した言明：
  (1) `vol_product`：すべての実数 n > 0 で Vol(S^(2n−1)_1) = Vol(S^(n−1)_1)·Vol(S^n_(1/2))。
      ルジャンドルの倍数公式（Mathlib の `Real.Gamma_mul_Gamma_add_half`）を代入するだけ。
  (2) `rho_eq_self_iff`：正の整数 n で ρ(n) = n ⇔ n ∈ {1, 2, 4, 8}（すべての n について）。
  (3) `lambda_mod_seven`：すべての整数 k（奇数に限らない）で 2(2k)²−1 ≡ k²−1 (mod 7)。
      `lambda_residues`：その余りは 0・1・3・6 のどれか。
      `lambda_zero_iff`：余りが 0 ⇔ k ≡ ±1 (mod 7)。
定義に置いたもの：半径 R の k 次元球面の体積 2π^((k+1)/2) R^k / Γ((k+1)/2)（原稿の設定の式そのまま）。
ρ(n) = 2^b + 8a（n = 2^(4a+b)·奇数、0 ≤ b ≤ 3。原稿の計算 4.1 の定義そのまま）。
λ の式 2p₁² − σ と、p₁ = ±2k・σ = 1 は原稿が書き写した既知の事実で、ここでは式 2(2k)²−1 だけを扱う。
形式化していないもの：ホップ束・ベクトル場・異種球面などの位相の中身（ρ が平行化可能性を表すこと
はアダムズの定理で、ここでは数の式だけを扱う）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1008

open Real

/-! ## (1) 体積の積 -/

/-- 半径 R の k 次元球面の体積（k は実数に広げる）。 -/
noncomputable def vol (k R : ℝ) : ℝ := 2 * π ^ ((k + 1) / 2) * R ^ k / Gamma ((k + 1) / 2)

/-- すべての実数 n > 0 で Vol(S^(2n−1)) = Vol(S^(n−1))·Vol(S^n_(1/2))。束の有無と無関係。 -/
theorem vol_product (n : ℝ) (hn : 0 < n) :
    vol (2 * n - 1) 1 = vol (n - 1) 1 * vol n (1 / 2) := by
  unfold vol
  have hdup := Real.Gamma_mul_Gamma_add_half (n / 2)
  have e1 : (2 * n - 1 + 1) / 2 = n := by ring
  have e2 : (n - 1 + 1) / 2 = n / 2 := by ring
  have e3 : n / 2 + 1 / 2 = (n + 1) / 2 := by ring
  have e4 : 2 * (n / 2) = n := by ring
  rw [e3, e4] at hdup
  rw [e1, e2]
  simp only [Real.one_rpow, mul_one]
  have hG1 : 0 < Gamma (n / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Gamma ((n + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG : 0 < Gamma n := Real.Gamma_pos_of_pos hn
  have hpi : 0 < π := Real.pi_pos
  have hp : π ^ (n / 2) * π ^ ((n + 1) / 2) = π ^ n * √π := by
    rw [← Real.rpow_add hpi, Real.sqrt_eq_rpow, ← Real.rpow_add hpi]
    ring_nf
  have h2 : (2 : ℝ) ^ (1 - n) = 2 * (1 / 2 : ℝ) ^ n := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.div_rpow (by norm_num) (by norm_num),
      Real.one_rpow]
    ring
  have hsq : 0 < √π := Real.sqrt_pos.mpr hpi
  have h12 : 0 < (1 / 2 : ℝ) ^ n := Real.rpow_pos_of_pos (by norm_num) n
  rw [h2] at hdup
  field_simp
  rw [mul_assoc, hdup]
  rw [show 2 * Gamma n * π ^ (n / 2) * π ^ ((n + 1) / 2) * (1 / 2) ^ n =
    2 * Gamma n * (π ^ (n / 2) * π ^ ((n + 1) / 2)) * (1 / 2) ^ n by ring, hp]
  ring

/-! ## (2) ラドン＝フルヴィッツ数 -/

/-- 2 で割れる回数を、燃料 f 回まで数える補助の関数。 -/
def v2aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n ≠ 0 ∧ n % 2 = 0 then v2aux f (n / 2) + 1 else 0

/-- n を割り切る 2 の冪の指数（n = 0 では 0 と置く）。燃料 n は足りる。 -/
def v2 (n : ℕ) : ℕ := v2aux n n

/-- ラドン＝フルヴィッツ数：n = 2^(4a+b)·奇数（0 ≤ b ≤ 3）のとき ρ(n) = 2^b + 8a。 -/
def rho (n : ℕ) : ℕ := 2 ^ (v2 n % 4) + 8 * (v2 n / 4)

/-- 原稿の表：n = 1〜16 の ρ(n) は 1,2,1,4,1,2,1,8,1,2,1,4,1,2,1,9。 -/
theorem rho_table : (List.range 16).map (fun i => rho (i + 1)) =
    [1, 2, 1, 4, 1, 2, 1, 8, 1, 2, 1, 4, 1, 2, 1, 9] := by
  decide

theorem v2aux_spec (f : ℕ) : ∀ n, 0 < n → n ≤ f → ∃ m, n = 2 ^ v2aux f n * m ∧ m % 2 = 1 := by
  induction f with
  | zero => intro n hn hf; omega
  | succ f ih =>
    intro n hn hf
    by_cases h : n % 2 = 0
    · obtain ⟨m, hm, hodd⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨m, ?_, hodd⟩
      have hv : v2aux (f + 1) n = v2aux f (n / 2) + 1 := by
        simp [v2aux, show n ≠ 0 by omega, h]
      rw [hv, pow_succ]
      calc n = 2 * (n / 2) := by omega
        _ = 2 ^ v2aux f (n / 2) * 2 * m := by conv_lhs => rw [hm]
                                              ring
    · refine ⟨n, ?_, by omega⟩
      have hv : v2aux (f + 1) n = 0 := by
        simp [v2aux, h]
      rw [hv]; simp

/-- 正の n は 2^(v2 n)·（奇数）と書ける。 -/
theorem v2_spec (n : ℕ) (hn : 0 < n) : ∃ m, n = 2 ^ v2 n * m ∧ m % 2 = 1 :=
  v2aux_spec n n hn le_rfl

theorem pow_gt_aux (a b : ℕ) (ha : 1 ≤ a) : 2 ^ b + 8 * a < 2 ^ (4 * a + b) := by
  have h16 : 1 + 15 * a ≤ 16 ^ a := by
    clear ha
    induction a with
    | zero => norm_num
    | succ a ih => rw [pow_succ]; nlinarith
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have : 2 ^ (4 * a + b) = 16 ^ a * 2 ^ b := by
    rw [pow_add, pow_mul]; norm_num
  rw [this]
  nlinarith

/-- ρ(n) = n となる正の整数は 1・2・4・8 だけ（すべての n について）。 -/
theorem rho_eq_self_iff (n : ℕ) (hn : 0 < n) : rho n = n ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  constructor
  · intro h
    obtain ⟨m, hm, hodd⟩ := v2_spec n hn
    have hm1 : 1 ≤ m := by omega
    set v := v2 n with hv
    unfold rho at h
    rw [← hv] at h
    by_cases hv4 : v < 4
    · have hb : v % 4 = v := Nat.mod_eq_of_lt hv4
      have ha : v / 4 = 0 := Nat.div_eq_of_lt hv4
      rw [hb, ha] at h
      have hpos : 0 < 2 ^ v := by positivity
      have : m = 1 := by
        have : 2 ^ v * m = 2 ^ v * 1 := by rw [← hm]; omega
        exact Nat.eq_of_mul_eq_mul_left hpos this
      subst this
      rw [mul_one] at hm
      clear h hodd hm1 hpos hb ha
      interval_cases v <;> omega
    · exfalso
      have ha : 1 ≤ v / 4 := by omega
      have hlt := pow_gt_aux (v / 4) (v % 4) ha
      have hvv : 4 * (v / 4) + v % 4 = v := Nat.div_add_mod v 4
      rw [hvv] at hlt
      have : 2 ^ v ≤ n := by rw [hm]; exact Nat.le_mul_of_pos_right _ hm1
      omega
  · rintro (rfl | rfl | rfl | rfl) <;> decide

/-! ## (3) ミルナーの λ の 7 の余り -/

/-- すべての整数 k で 2(2k)² − 1 ≡ k² − 1 (mod 7)（8 ≡ 1 (mod 7) から）。 -/
theorem lambda_mod_seven (k : ℤ) : 2 * (2 * k) ^ 2 - 1 ≡ k ^ 2 - 1 [ZMOD 7] := by
  have h : k ^ 2 - 1 ≡ 2 * (2 * k) ^ 2 - 1 [ZMOD 7] :=
    Int.modEq_iff_dvd.mpr ⟨k ^ 2, by ring⟩
  exact h.symm

/-- 余りは 0・1・3・6 のどれか。 -/
theorem lambda_residues (k : ℤ) :
    (2 * (2 * k) ^ 2 - 1) % 7 = 0 ∨ (2 * (2 * k) ^ 2 - 1) % 7 = 1 ∨
    (2 * (2 * k) ^ 2 - 1) % 7 = 3 ∨ (2 * (2 * k) ^ 2 - 1) % 7 = 6 := by
  rw [lambda_mod_seven k]
  have h0 := Int.emod_nonneg k (show (7 : ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos k (show (0 : ℤ) < 7 by norm_num)
  have key : (k ^ 2 - 1) % 7 = ((k % 7) ^ 2 - 1) % 7 :=
    (((Int.mod_modEq k 7).symm.pow 2).sub_right 1 : _)
  rw [key]
  generalize k % 7 = r at h0 h1 ⊢
  interval_cases r <;> decide

/-- 余りが 0 ⇔ k ≡ 1 または k ≡ −1 (mod 7)。 -/
theorem lambda_zero_iff (k : ℤ) :
    (2 * (2 * k) ^ 2 - 1) % 7 = 0 ↔ k % 7 = 1 ∨ k % 7 = 6 := by
  rw [lambda_mod_seven k]
  have h0 := Int.emod_nonneg k (show (7 : ℤ) ≠ 0 by norm_num)
  have h1 := Int.emod_lt_of_pos k (show (0 : ℤ) < 7 by norm_num)
  have key : (k ^ 2 - 1) % 7 = ((k % 7) ^ 2 - 1) % 7 :=
    (((Int.mod_modEq k 7).symm.pow 2).sub_right 1 : _)
  rw [key]
  generalize k % 7 = r at h0 h1 ⊢
  interval_cases r <;> decide

end Paper1008

end Yamagishi
