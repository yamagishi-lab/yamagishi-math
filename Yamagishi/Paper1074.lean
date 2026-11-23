/-
論文1074『同じ行列が、連続の上では混ぜ続け、画素の上では必ず絵を元に戻す』の格上げ（一般の形）。

日本語の一文：猫写像 [[2,1],[1,1]] で N×N の画素がすべて k 回で元に戻るのは、k が奇数なら N が
リュカ数 L_k を割るとき、k が偶数なら N がフィボナッチ数 F_k を割るときに限る。
English: For the cat map A = [[2,1],[1,1]] on (ℤ/N)², all pixels return after k ≥ 1 steps iff
N ∣ L_k (k odd) or N ∣ F_k (k even); hence N ≤ L_k, the return time is m for N = L_m (m odd ≥ 3)
and N = F_m (m even ≥ 4), 2m for N = F_m (m odd ≥ 5) and N = L_m (m even ≥ 2), and A^j ≡ F_(2j−1)·I
whenever A^(2j) ≡ I.

原稿（1074_yamagishi_the_same_matrix_mixes_the_continuum_and_returns_the_pixels/…_jp.tex）は、
N = 2〜300 で戻る回数 T(N) を数え、ピサノ周期と突き合わせ、フィボナッチ数とリュカ数の N を 8 個ずつ
表にし（144 は 12 回、199 は 11 回）、半分の回で単位行列の定数倍になる N を数えている
（144 の 6 回目は 89 倍）。一般の規則は導いていないと書いている。

ここで証明した言明（N は任意の自然数、画素は ZMod N の組）：
  (1) `pixels_return_iff`：すべての画素が k 回で戻る ⇔ 行列として A^k = I（mod N）。
  (2) `return_iff_odd`：k 奇数なら A^k = I ⇔ N ∣ L_k。`return_iff_even`：k 偶数なら ⇔ N ∣ F_k。
  (3) `le_luc_of_return`：k ≥ 1 で A^k = I なら N ≤ L_k（戻るにはリュカ数が N に届く回数が要る）。
  (4) `half_scalar`：A^(2j) = I なら A^j = F_(2j−1)·I（半分の回は単位行列の定数倍）。
      `example_144`：N = 144 で A^6 = 89·I、89² ≡ 1。
  (5) 戻る回数（A^k = I となる最小の k ≥ 1）：
      `period_luc_odd`：N = L_m（m 奇数 ≥ 3）で m。`period_fib_even`：N = F_m（m 偶数 ≥ 4）で m。
      `period_fib_odd`：N = F_m（m 奇数 ≥ 5）で 2m。`period_luc_even`：N = L_m（m 偶数 ≥ 2）で 2m。
      `period_two`：N = F_3 = 2 は例外で 3。`period_144`・`period_199`：144 は 12、199 は 11。
足した仮定：なし（N = 1 も含めて成り立つ）。リュカ数は L_0 = 2、L_1 = 1、L_(n+2) = L_n + L_(n+1) と定義した。
形式化していないもの：ピサノ周期との関係、T(N) ≤ 3N（ダイソンとフォーク）、連続の上で混ぜること、
丸めの誤差の育ち方、輪の数え上げ、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1074

open Nat Matrix

/-! ### リュカ数とフィボナッチ数の式 -/

/-- リュカ数 L_0 = 2、L_1 = 1、L_(n+2) = L_n + L_(n+1)。 -/
def luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => luc n + luc (n + 1)

theorem luc_add_fib (n : ℕ) : luc n + fib n = 2 * fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [luc]
    | 1 => simp [luc]
    | (n + 2) =>
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      simp only [luc]
      rw [fib_add_two, show n + 2 + 1 = (n + 1) + 2 by ring, fib_add_two, fib_add_two]
      rw [show n + 1 + 1 = n + 2 by ring, fib_add_two] at h2
      linarith

theorem luc_pos (n : ℕ) : 0 < luc n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [luc]
    | 1 => simp [luc]
    | (n + 2) => simp only [luc]; have := ih n (by omega); omega

theorem luc_succ_lt (n : ℕ) : luc (n + 1) < luc (n + 2) := by
  simp only [luc]; have := luc_pos n; omega

/-- L は 1 から先で狭義に増える。 -/
theorem luc_lt_luc {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : luc a < luc b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · have := ih h
      obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
      exact this.trans (luc_succ_lt c)
    · subst h
      obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
      exact luc_succ_lt c

theorem fib_le_luc (n : ℕ) : fib n ≤ luc n := by
  have := luc_add_fib n
  have := fib_le_fib_succ (n := n)
  omega

theorem fib_lt_luc {n : ℕ} (hn : 2 ≤ n) : fib n < luc n := by
  have := luc_add_fib n
  have := fib_lt_fib_succ hn
  omega

/-- 隣り合うリュカ数は互いに素。 -/
theorem luc_coprime (n : ℕ) : Nat.Coprime (luc n) (luc (n + 1)) := by
  induction n with
  | zero => simp [luc]
  | succ n ih =>
    show Nat.Coprime (luc (n + 1)) (luc (n + 2))
    simp only [luc]
    rw [Nat.coprime_add_self_right]
    exact ih.symm

/-- F(m+1)² − F(m+1)F(m) − F(m)² = (−1)^m（カッシーニの式の形）。 -/
theorem cassini (m : ℕ) :
    (fib (m + 1) : ℤ) ^ 2 - fib (m + 1) * fib m - (fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 by ring, fib_add_two, pow_succ]
    push_cast
    linear_combination (-1 : ℤ) * ih

/-- F(2n) = F(n)·L(n)。 -/
theorem fib_two_mul_eq (n : ℕ) : fib (2 * n) = fib n * luc n := by
  rw [fib_two_mul]
  congr 1
  have := luc_add_fib n
  omega

/-- m 偶数：F(2m+1) = L(m+1)F(m) + 1。 -/
theorem fib_odd_even {m : ℕ} (hm : Even m) : fib (2 * m + 1) = luc (m + 1) * fib m + 1 := by
  have hL : (luc (m + 1) : ℤ) = 2 * fib (m + 2) - fib (m + 1) := by
    have := luc_add_fib (m + 1); push_cast [show m + 1 + 1 = m + 2 by ring] at this ⊢; linarith
  have hF : (fib (2 * m + 1) : ℤ) = fib (m + 1) ^ 2 + fib m ^ 2 := by
    rw [fib_two_mul_add_one]; push_cast; ring
  have hc := cassini m
  rw [hm.neg_one_pow] at hc
  have h2 : (fib (m + 2) : ℤ) = fib m + fib (m + 1) := by rw [fib_add_two]; push_cast; ring
  have : (fib (2 * m + 1) : ℤ) = (luc (m + 1) * fib m + 1 : ℕ) := by
    push_cast
    rw [hF, hL, h2]
    linear_combination hc
  exact_mod_cast this

/-- m 奇数：F(2m+1) = F(m+1)L(m) + 1。 -/
theorem fib_odd_odd {m : ℕ} (hm : Odd m) : fib (2 * m + 1) = fib (m + 1) * luc m + 1 := by
  have hL : (luc m : ℤ) = 2 * fib (m + 1) - fib m := by
    have : (luc m : ℤ) + fib m = 2 * fib (m + 1) := by exact_mod_cast luc_add_fib m
    linarith
  have hF : (fib (2 * m + 1) : ℤ) = fib (m + 1) ^ 2 + fib m ^ 2 := by
    rw [fib_two_mul_add_one]; push_cast; ring
  have hc := cassini m
  rw [hm.neg_one_pow] at hc
  have : (fib (2 * m + 1) : ℤ) = (fib (m + 1) * luc m + 1 : ℕ) := by
    push_cast
    rw [hF, hL]
    linear_combination (-1 : ℤ) * hc
  exact_mod_cast this

/-! ### 画素の上の猫写像 -/

/-- フィボナッチ行列 Q = [[1,1],[1,0]]（mod N）。 -/
def Q (N : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 1; 1, 0]

/-- 猫写像の行列 A = [[2,1],[1,1]]（mod N）。画素 (x, y) を (2x + y, x + y) へ送る。 -/
def A (N : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod N) := !![2, 1; 1, 1]

theorem A_eq_sq (N : ℕ) : A N = Q N ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, Q, sq, Matrix.mul_apply, Fin.sum_univ_two]

theorem Q_pow (N n : ℕ) :
    Q N ^ (n + 1) = !![(fib (n + 2) : ZMod N), fib (n + 1); fib (n + 1), fib n] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [Q]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two, fib_add_two] <;> ring

theorem A_pow (N m : ℕ) :
    A N ^ (m + 1) =
      !![(fib (2 * m + 3) : ZMod N), fib (2 * m + 2); fib (2 * m + 2), fib (2 * m + 1)] := by
  rw [A_eq_sq, ← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Q_pow]

/-- (1) すべての画素が k 回で戻る ⇔ A^k = I（mod N）。 -/
theorem pixels_return_iff (N k : ℕ) :
    (∀ v : Fin 2 → ZMod N, (A N ^ k) *ᵥ v = v) ↔ A N ^ k = 1 := by
  constructor
  · intro h
    ext i j
    have hv := congrFun (h (Pi.single j 1)) i
    rw [mulVec_single_one] at hv
    rw [Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simpa using hv
  · intro h v
    rw [h, one_mulVec]

/-- A^(m+1) = I ⇔ N ∣ F(2m+2) かつ F(2m+1) ≡ 1。 -/
theorem return_iff_fib (N m : ℕ) :
    A N ^ (m + 1) = 1 ↔ N ∣ fib (2 * m + 2) ∧ (fib (2 * m + 1) : ZMod N) = 1 := by
  rw [A_pow]
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h11 := congrFun (congrFun h 1) 1
    simp at h01 h11
    exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp h01, h11⟩
  · rintro ⟨h1, h2⟩
    have h0 : (fib (2 * m + 2) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    have h3 : (fib (2 * m + 3) : ZMod N) = 1 := by
      rw [show 2 * m + 3 = (2 * m + 1) + 2 by ring, fib_add_two]
      push_cast
      rw [h2, show 2 * m + 1 + 1 = 2 * m + 2 by ring, h0]
      ring
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h2, h3]

theorem cast_succ_eq_one_iff (N X : ℕ) : ((X + 1 : ℕ) : ZMod N) = 1 ↔ N ∣ X := by
  push_cast
  rw [add_eq_right, ZMod.natCast_eq_zero_iff]

/-- (2) k 奇数：A^k = I ⇔ N ∣ L_k。 -/
theorem return_iff_odd (N : ℕ) {k : ℕ} (hk : Odd k) : A N ^ k = 1 ↔ N ∣ luc k := by
  obtain ⟨j, rfl⟩ := hk
  have hm : Even (2 * j) := even_two_mul j
  rw [return_iff_fib, fib_odd_even hm, cast_succ_eq_one_iff,
    show 2 * (2 * j) + 2 = 2 * (2 * j + 1) by ring, fib_two_mul_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : N ∣ luc (2 * j + 1) * fib (2 * j + 1) := by rw [mul_comm]; exact h1
    have h := Nat.dvd_gcd h1' h2
    rwa [Nat.gcd_mul_left, (fib_coprime_fib_succ (2 * j)).symm.gcd_eq_one, mul_one] at h
  · intro h
    exact ⟨Dvd.dvd.mul_left h _, Dvd.dvd.mul_right h _⟩

/-- (2) k 偶数：A^k = I ⇔ N ∣ F_k。 -/
theorem return_iff_even (N : ℕ) {k : ℕ} (hk : Even k) : A N ^ k = 1 ↔ N ∣ fib k := by
  obtain ⟨j, rfl⟩ := hk
  rcases j with _ | j
  · simp
  have hm : Odd (2 * j + 1) := odd_two_mul_add_one j
  rw [show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, return_iff_fib, fib_odd_odd hm,
    cast_succ_eq_one_iff, show 2 * (2 * j + 1) + 2 = 2 * (2 * j + 1 + 1) by ring, fib_two_mul_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h := Nat.dvd_gcd h1 h2
    rwa [Nat.gcd_mul_left, (luc_coprime (2 * j + 1)).symm.gcd_eq_one, mul_one] at h
  · intro h
    exact ⟨Dvd.dvd.mul_right h _, Dvd.dvd.mul_right h _⟩

/-- (3) k ≥ 1 で戻るなら N ≤ L_k。 -/
theorem le_luc_of_return {N k : ℕ} (hk : 0 < k) (h : A N ^ k = 1) : N ≤ luc k := by
  rcases Nat.even_or_odd k with he | ho
  · have := (return_iff_even N he).mp h
    exact (Nat.le_of_dvd (fib_pos.mpr hk) this).trans (fib_le_luc k)
  · exact Nat.le_of_dvd (luc_pos k) ((return_iff_odd N ho).mp h)

/-- (4) A^(2j) = I なら A^j = F_(2j−1)·I（j ≥ 1）。 -/
theorem half_scalar (N j : ℕ) (h : A N ^ (2 * (j + 1)) = 1) :
    A N ^ (j + 1) = (fib (2 * j + 1) : ZMod N) • (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  have hd := (return_iff_even N (even_two_mul (j + 1))).mp h
  have h0 : (fib (2 * j + 2) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have h3 : (fib (2 * j + 3) : ZMod N) = fib (2 * j + 1) := by
    rw [show 2 * j + 3 = (2 * j + 1) + 2 by ring, fib_add_two]
    push_cast
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring, h0, add_zero]
  rw [A_pow]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [h0, h3]

theorem fib_twelve : fib 12 = 144 := by decide

theorem luc_eleven : luc 11 = 199 := by decide

/-- (4) 144 画素の 6 回目は単位行列の 89 倍で、89² ≡ 1（mod 144）。 -/
theorem example_144 :
    A 144 ^ 6 = (89 : ZMod 144) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 144)) ∧
      (89 : ZMod 144) ^ 2 = 1 := by
  refine ⟨?_, by decide⟩
  have h12 : A 144 ^ (2 * (5 + 1)) = 1 :=
    (return_iff_even 144 (even_two_mul (5 + 1))).mpr (by rw [show 2 * (5 + 1) = 12 by rfl,
      fib_twelve])
  have := half_scalar 144 5 h12
  rw [show (fib (2 * 5 + 1) : ZMod 144) = 89 by
    rw [show 2 * 5 + 1 = 11 by rfl, show fib 11 = 89 by decide]; rfl] at this
  exact this

/-! ### 戻る回数 -/

/-- 戻る回数の集合（k ≥ 1 で A^k = I）。最小の元が戻る回数 T(N)。 -/
def returns (N : ℕ) : Set ℕ := {k | 0 < k ∧ A N ^ k = 1}

/-- 1 ≤ g < m、m ≥ 3 なら F_m は F_g を割らない。 -/
theorem fib_not_dvd {g m : ℕ} (hg : 0 < g) (hgm : g < m) (hm : 3 ≤ m) : ¬ fib m ∣ fib g := by
  intro h
  have h1 : fib g ≤ fib (m - 1) := fib_mono (by omega)
  have h2 : fib (m - 1) < fib m := by
    have := fib_lt_fib_succ (n := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this
  have := Nat.le_of_dvd (fib_pos.mpr hg) h
  omega

theorem fib_dvd_fib_gcd {x a b : ℕ} (ha : x ∣ fib a) (hb : x ∣ fib b) : x ∣ fib (Nat.gcd a b) := by
  rw [fib_gcd]; exact Nat.dvd_gcd ha hb

/-- 真の約数は半分以下。 -/
theorem two_mul_le_of_dvd {g n : ℕ} (hd : g ∣ n) (hlt : g < n) : 2 * g ≤ n := by
  obtain ⟨t, rfl⟩ := hd
  rcases t with _ | _ | t
  · simp at hlt
  · simp at hlt
  · nlinarith

/-- (5) N = L_m（m 奇数 ≥ 3）なら戻る回数は m。 -/
theorem period_luc_odd {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) : IsLeast (returns (luc m)) m := by
  refine ⟨⟨by omega, (return_iff_odd _ hm).mpr dvd_rfl⟩, ?_⟩
  rintro k ⟨hk, hA⟩
  by_contra hlt
  push Not at hlt
  rcases Nat.even_or_odd k with he | ho
  · have h := (return_iff_even _ he).mp hA
    have := Nat.le_of_dvd (fib_pos.mpr hk) h
    have := fib_mono hlt.le
    have := fib_lt_luc (n := m) (by omega)
    omega
  · have h := (return_iff_odd _ ho).mp hA
    have := Nat.le_of_dvd (luc_pos k) h
    have := luc_lt_luc hk hlt
    omega

/-- (5) N = F_m（m 偶数 ≥ 4）なら戻る回数は m。 -/
theorem period_fib_even {m : ℕ} (hm : Even m) (h4 : 4 ≤ m) : IsLeast (returns (fib m)) m := by
  refine ⟨⟨by omega, (return_iff_even _ hm).mpr dvd_rfl⟩, ?_⟩
  rintro k ⟨hk, hA⟩
  by_contra hlt
  push Not at hlt
  rcases Nat.even_or_odd k with he | ho
  · exact fib_not_dvd hk hlt (by omega) ((return_iff_even _ he).mp hA)
  · have h := (return_iff_odd _ ho).mp hA
    have h2k : fib m ∣ fib (2 * k) := by rw [fib_two_mul_eq]; exact Dvd.dvd.mul_left h _
    have hg := fib_dvd_fib_gcd (dvd_refl (fib m)) h2k
    have hgpos : 0 < Nat.gcd m (2 * k) := Nat.gcd_pos_of_pos_left _ (by omega)
    rcases lt_or_eq_of_le (Nat.gcd_le_left (2 * k) (by omega : 0 < m)) with hgl | hge
    · exact fib_not_dvd hgpos hgl (by omega) hg
    · -- m ∣ 2k かつ 2k < 2m なので m = 2k
      have hmd : m ∣ 2 * k := by rw [← hge]; exact Nat.gcd_dvd_right m (2 * k)
      obtain ⟨t, ht⟩ := hmd
      have hm2k : m = 2 * k := by
        rcases t with _ | _ | t
        · omega
        · omega
        · nlinarith
      rw [hm2k, fib_two_mul_eq] at h
      have hle := Nat.le_of_dvd (luc_pos k) h
      have hL := luc_pos k
      have hf1 : fib k ≤ 1 := by
        by_contra hc; push Not at hc; nlinarith
      have hk2 : k ≤ 2 := by
        by_contra hc; push Not at hc
        have := fib_mono (show 3 ≤ k by omega)
        have h3 : fib 3 = 2 := by decide
        omega
      obtain ⟨r, hr⟩ := ho
      omega

/-- (5) N = F_m（m 奇数 ≥ 5）なら戻る回数は 2m。 -/
theorem period_fib_odd {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m) : IsLeast (returns (fib m)) (2 * m) := by
  refine ⟨⟨by omega, (return_iff_even _ (even_two_mul m)).mpr
    (fib_dvd m (2 * m) (dvd_mul_left m 2))⟩, ?_⟩
  rintro k ⟨hk, hA⟩
  by_contra hlt
  push Not at hlt
  have hcop : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hm
  rcases Nat.even_or_odd k with he | ho
  · have h := (return_iff_even _ he).mp hA
    have hg := fib_dvd_fib_gcd (dvd_refl (fib m)) h
    have hgpos : 0 < Nat.gcd m k := Nat.gcd_pos_of_pos_left _ (by omega)
    rcases lt_or_eq_of_le (Nat.gcd_le_left k (by omega : 0 < m)) with hgl | hge
    · exact fib_not_dvd hgpos hgl (by omega) hg
    · have hmd : m ∣ k := by rw [← hge]; exact Nat.gcd_dvd_right m k
      have h2d : 2 ∣ k := even_iff_two_dvd.mp he
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2d hmd
      have := Nat.le_of_dvd hk this
      omega
  · have h := (return_iff_odd _ ho).mp hA
    have h2k : fib m ∣ fib (2 * k) := by rw [fib_two_mul_eq]; exact Dvd.dvd.mul_left h _
    have hg := fib_dvd_fib_gcd (dvd_refl (fib m)) h2k
    have hgpos : 0 < Nat.gcd m (2 * k) := Nat.gcd_pos_of_pos_left _ (by omega)
    rcases lt_or_eq_of_le (Nat.gcd_le_left (2 * k) (by omega : 0 < m)) with hgl | hge
    · exact fib_not_dvd hgpos hgl (by omega) hg
    · have hmd : m ∣ 2 * k := by rw [← hge]; exact Nat.gcd_dvd_right m (2 * k)
      have hmk : m ∣ k := hcop.symm.dvd_of_dvd_mul_left hmd
      obtain ⟨t, ht⟩ := hmk
      have hkm : k = m := by
        rcases t with _ | _ | t
        · omega
        · omega
        · nlinarith
      rw [hkm] at h
      -- F_m ∣ L_m なら F_m ∣ 2F_(m+1)、互いに素なので F_m ∣ 2
      have h2 : fib m ∣ 2 * fib (m + 1) := by
        rw [← luc_add_fib]; exact Nat.dvd_add h dvd_rfl
      have h3 : fib m ∣ 2 := (fib_coprime_fib_succ m).dvd_of_dvd_mul_right h2
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5' : fib 5 ≤ fib m := fib_mono h5
      have : fib 5 = 5 := by decide
      omega

/-- (5) N = L_m（m 偶数 ≥ 2）なら戻る回数は 2m。 -/
theorem period_luc_even {m : ℕ} (hm : Even m) (h2 : 2 ≤ m) : IsLeast (returns (luc m)) (2 * m) := by
  have hmem : luc m ∣ fib (2 * m) := by rw [fib_two_mul_eq]; exact dvd_mul_left _ _
  refine ⟨⟨by omega, (return_iff_even _ (even_two_mul m)).mpr hmem⟩, ?_⟩
  rintro k ⟨hk, hA⟩
  by_contra hlt
  push Not at hlt
  have hFL : fib m < luc m := fib_lt_luc h2
  rcases Nat.even_or_odd k with he | ho
  · have h := (return_iff_even _ he).mp hA
    have hg := fib_dvd_fib_gcd h hmem
    have hgpos : 0 < Nat.gcd k (2 * m) := Nat.gcd_pos_of_pos_left _ hk
    have hgl : Nat.gcd k (2 * m) < 2 * m := lt_of_le_of_lt (Nat.gcd_le_left _ hk) hlt
    have hg2 := two_mul_le_of_dvd (Nat.gcd_dvd_right k (2 * m)) hgl
    have := Nat.le_of_dvd (fib_pos.mpr hgpos) hg
    have := fib_mono (show Nat.gcd k (2 * m) ≤ m by omega)
    omega
  · have h := (return_iff_odd _ ho).mp hA
    have h2k : luc m ∣ fib (2 * k) := by rw [fib_two_mul_eq]; exact Dvd.dvd.mul_left h _
    have hg := fib_dvd_fib_gcd h2k hmem
    rw [Nat.gcd_mul_left] at hg
    have hgpos : 0 < Nat.gcd k m := Nat.gcd_pos_of_pos_left _ hk
    -- gcd(k, m) は奇数（k を割る）で m は偶数なので、gcd < m
    have hgodd : Odd (Nat.gcd k m) := Odd.of_dvd_nat ho (Nat.gcd_dvd_left k m)
    have hgne : Nat.gcd k m ≠ m := by
      intro he'; rw [he'] at hgodd; exact (Nat.not_even_iff_odd.mpr hgodd) hm
    have hgl : Nat.gcd k m < m := lt_of_le_of_ne (Nat.gcd_le_right _ (by omega)) hgne
    have hg2 := two_mul_le_of_dvd (Nat.gcd_dvd_right k m) hgl
    have := Nat.le_of_dvd (fib_pos.mpr (by omega)) hg
    have := fib_mono hg2
    omega

/-- (5) N = F_3 = 2 は例外で、戻る回数は 3（2m = 6 ではない）。 -/
theorem period_two : IsLeast (returns 2) 3 := by
  refine ⟨⟨by norm_num, (return_iff_odd 2 (by decide)).mpr (by decide)⟩, ?_⟩
  rintro k ⟨hk, hA⟩
  by_contra hlt
  push Not at hlt
  interval_cases k
  · exact absurd ((return_iff_odd 2 (by decide)).mp hA) (by decide)
  · exact absurd ((return_iff_even 2 (by decide)).mp hA) (by decide)

/-- 144 = F_12 の画素は 12 回で戻る。 -/
theorem period_144 : IsLeast (returns 144) 12 := by
  rw [← fib_twelve]; exact period_fib_even (by decide) (by norm_num)

/-- 199 = L_11 の画素は 11 回で戻る。 -/
theorem period_199 : IsLeast (returns 199) 11 := by
  rw [← luc_eleven]; exact period_luc_odd (by decide) (by norm_num)

end Paper1074

end Yamagishi
