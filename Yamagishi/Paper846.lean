/-
論文846『勝てるかどうかは後ろから塗れば分かる。何手で勝てるかは、その札からは読めない』の格上げ（一般の形）。

原稿（846_yamagishi_whether_you_can_win_and_in_how_many_moves/…_jp.tex）は、取れる数 {1, 3, 4} の
一山の減算ゲームを位置 0〜1000 まで後ろから塗り、負け局面 286 個がすべて 7 を法として 0 か 2 で、
法に合う位置はすべて負けだと両向きに数えている（「周期 7 の証明はしない」と明記）。
手数は六つの位置の表（10 で 5、20 で 11、50 で 29、100 で 58、500 で 285、1000 で 571）。

ここで証明した言明（すべての自然数 n）：
  (1) `lose_iff`：n が負け局面 ⇔ n mod 7 が 0 か 2。
  (2) `remoteness_formula`：最善の手数（勝つ側は最短、負ける側は最長に引き延ばす手数。
      シュタインハウスの remoteness）は r(n) = 4⌊n/7⌋ + c(n mod 7)、c = (0, 1, 2, 1, 1, 3, 3)。
  (3) `remoteness_odd_iff_win`：r(n) が奇数 ⇔ n は勝ち局面。
  (4) 原稿の表の六つの手数は (2) の式の値と一致する（`table_values`）。
定義に置いたもの：勝ち win(n) = 「取れる手のどれかで相手を負け局面に送れる」（原稿の式そのまま）。
手数 rem(n) は、n = 0 で 0、勝ち局面なら 1 + （負け局面へ送る手の先の手数の最小）、負け局面なら
1 + （すべての手の先の手数の最大）。最小をとる所では、負けの先でない手に大きな番兵の値を置いた。
形式化していないもの：前から探したときに見る局面の数、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper846

/-- 勝ち局面：取れる手のどれかで、相手を負け局面に送れる。 -/
def win (n : ℕ) : Bool :=
  (if h : 1 ≤ n then !win (n - 1) else false) ||
  (if h : 3 ≤ n then !win (n - 3) else false) ||
  (if h : 4 ≤ n then !win (n - 4) else false)
termination_by n
decreasing_by all_goals omega

/-- 負け局面の判定式。 -/
def L (n : ℕ) : Prop := n % 7 = 0 ∨ n % 7 = 2

instance (n : ℕ) : Decidable (L n) := by unfold L; infer_instance

theorem win0 : win 0 = false := by rw [win]; simp
theorem win1 : win 1 = true := by rw [win]; simp [win0]
theorem win2 : win 2 = false := by rw [win]; simp [win1]
theorem win3 : win 3 = true := by rw [win]; simp [win0]

/-- (1) 負け局面 ⇔ n mod 7 ∈ {0, 2}。 -/
theorem win_eq (n : ℕ) : win n = !decide (L n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [win]
    have h1 : ∀ m, m ≤ n → 1 ≤ m → win (n - m) = !decide (L (n - m)) :=
        fun m _ hm => ih _ (by omega)
    by_cases a1 : 1 ≤ n
    · by_cases a3 : 3 ≤ n
      · by_cases a4 : 4 ≤ n
        · simp only [a1, a3, a4, dite_true, h1 1 a1 le_rfl,
            h1 3 a3 (by norm_num), h1 4 a4 (by norm_num)]
          unfold L
          by_cases c : n % 7 = 0 ∨ n % 7 = 2 <;>
          by_cases c1 : (n - 1) % 7 = 0 ∨ (n - 1) % 7 = 2 <;>
          by_cases c3 : (n - 3) % 7 = 0 ∨ (n - 3) % 7 = 2 <;>
          by_cases c4 : (n - 4) % 7 = 0 ∨ (n - 4) % 7 = 2 <;>
          simp only [c, c1, c3, c4, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.or_true, Bool.or_false] <;> omega
        · have : n = 3 := by omega
          subst this; rw [← win]; rw [win3]; decide
      · interval_cases n
        · rw [← win, win1]; decide
        · rw [← win, win2]; decide
    · have : n = 0 := by omega
      subst this; rw [← win, win0]; decide

theorem lose_iff (n : ℕ) : win n = false ↔ L n := by
  rw [win_eq]; by_cases h : L n <;> simp [h]

/-- 番兵の値（どの手数よりも大きい）。 -/
def big (n : ℕ) : ℕ := 10 * n + 10

/-- 手数（remoteness）。 -/
def rem (n : ℕ) : ℕ :=
  if h0 : n = 0 then 0 else
  if win n then
    1 + min (if !win (n - 1) then rem (n - 1) else big n)
      (min (if h : 3 ≤ n then (if !win (n - 3) then rem (n - 3) else big n) else big n)
           (if h : 4 ≤ n then (if !win (n - 4) then rem (n - 4) else big n) else big n))
  else
    1 + max (rem (n - 1))
      (max (if h : 3 ≤ n then rem (n - 3) else 0) (if h : 4 ≤ n then rem (n - 4) else 0))
termination_by n
decreasing_by all_goals omega

/-- 閉じた式の c。 -/
def c (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else if k = 3 then 1 else
  if k = 4 then 1 else 3

/-- 閉じた式 r(n) = 4⌊n/7⌋ + c(n mod 7)。 -/
def r (n : ℕ) : ℕ := 4 * (n / 7) + c (n % 7)

theorem rem0 : rem 0 = 0 := by rw [rem]; simp
theorem rem1 : rem 1 = 1 := by rw [rem]; simp [win1, win0, rem0]
theorem rem2 : rem 2 = 2 := by rw [rem]; simp [win2, rem1]
theorem rem3 : rem 3 = 1 := by rw [rem]; simp [win3, win2, win0, rem2, rem0, big]

/-- (2) 手数の閉じた式。 -/
theorem remoteness_formula (n : ℕ) : rem n = r n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 4
    · interval_cases n
      · rw [rem0]; decide
      · rw [rem1]; decide
      · rw [rem2]; decide
      · rw [rem3]; decide
    · push Not at hn
      have e1 := ih (n - 1) (by omega)
      have e3 := ih (n - 3) (by omega)
      have e4 := ih (n - 4) (by omega)
      have a3 : 3 ≤ n := by omega
      rw [rem]
      simp only [show n ≠ 0 by omega, dite_false, a3, hn, dite_true, e1, e3, e4]
      rw [win_eq n, win_eq (n - 1), win_eq (n - 3), win_eq (n - 4)]
      simp only [L, r]
      have h1 : (n - 1) % 7 = (n % 7 + 6) % 7 := by omega
      have h3 : (n - 3) % 7 = (n % 7 + 4) % 7 := by omega
      have h4 : (n - 4) % 7 = (n % 7 + 3) % 7 := by omega
      simp only [h1, h3, h4]
      rcases (show n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨
          n % 7 = 6 by omega) with h | h | h | h | h | h | h <;>
      · simp only [h]; norm_num [c, big]; omega

/-- (3) 手数が奇数 ⇔ 勝ち局面。 -/
theorem remoteness_odd_iff_win (n : ℕ) : rem n % 2 = 1 ↔ win n = true := by
  rw [remoteness_formula, win_eq]
  unfold r c L
  split_ifs <;> simp <;> omega

/-- (4) 原稿の表の六つの手数。 -/
theorem table_values : r 10 = 5 ∧ r 20 = 11 ∧ r 50 = 29 ∧
    r 100 = 58 ∧ r 500 = 285 ∧ r 1000 = 571 := by
  decide

end Paper846

end Yamagishi
