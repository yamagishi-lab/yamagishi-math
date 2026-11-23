/-
論文908『電子の電磁質量の 4/3 は、球の体積ではなく場の向きの平均から来る』の格上げ（芯だけ）。

日本語の一文：場のエネルギーと運動量を静止系の角度の積分に直した形を入力に置くと、d 次元の球面の
本物の測度で平均して、どの速さでも p = 2(1 − 1/d)γβU₀、U = γU₀(1 + (1 − 2/d)β²) が厳密に出て、
場だけで 4 元ベクトルになるのは d = 2 のときに限る。
English: Core only: taking the field energy and momentum written as rest-frame angular integrals as
input, the surface measure of S^(d−1) gives, for every β < 1, p = 2(1 − 1/d)γβU₀ and
U = γU₀(1 + (1 − 2/d)β²); p/(γβ) = U/γ iff d = 2; the ball-volume coefficient V_d/π^⌊d/2⌋ equals
2(1 − 1/d) only for d = 2, 3.

原稿（908_yamagishi_electromagnetic_mass_four_thirds_is_twice_the_directional_average/…_jp.tex）は、
d = 3 で β = 0.1・0.5・0.9 の三つを三次元の格子で数値積分して閉じた式と合わせ、⟨sin²θ⟩ = 1 − 1/d を
d = 2〜6 で数値で出して比 2(1 − 1/d) と球の体積の係数を並べている。d 次元のエネルギーの式は無い。

ここで証明した言明（d ≥ 1、0 ≤ β < 1、γ = 1/√(1 − β²)、動く向きは座標 i）：
  (1) `momentum_eq`：p = 2(1 − 1/d)γβU₀。`energy_eq`：U = γU₀(1 + (1 − 2/d)β²)。
      `three_dim`：d = 3 で p = (4/3)γβU₀、U = γU₀(1 + β²/3)。
  (2) `four_vector_iff`：0 < β < 1、d ≥ 1 で p/(γβ) = U/γ ⇔ d = 2。
  (3) `paper_formula_iff`：原稿の計算 3.1 の形 p = β·2⟨sin²θ⟩·U（U は動く場のエネルギー）は、
      d ≥ 2・U₀ > 0 で β = 0 か d = 2 のときに限って正しい（d = 3、β = 0.5 では 4/3·0.5·U ≠ p）。
  (4) `ball_coeff_eq_iff`：d ≥ 2 で、球の体積の係数 V_d/π^⌊d/2⌋ が 2(1 − 1/d) に等しい ⇔ d = 2 か 3。
足した仮定（ここが「芯だけ」の理由）：静止系の座標で、場の大きさが半径だけの関数 e(r) で向きが動径と
いう球対称の場を置き、ローレンツ変換（平行成分はそのまま、垂直成分は γ 倍、B = β × E、dV = dV′/γ）で
得られる密度を、半径の積分 K = ∫e(r)² r^(d−1) dr と球面の積分の積に分けた形
  U₀ = K/(8π)·∮1 dS、U = K/(8πγ)·∮(n_i² + γ²(1 + β²)(1 − n_i²)) dS、p = βγK/(4π)·∮(1 − n_i²) dS
を定義として置いた。場の変換と極座標での分け方は形式化していない（d ≥ 4 での E × B の読み替えも
原稿と同じ置き方）。球面の測度と ∮ n_i² dS = V_d、∮ 1 dS = d·V_d は論文912 のファイルの定理を使った。
形式化していないもの：d ≤ 2 でエネルギーが発散すること、ポアンカレ応力、数値積分の表、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper912

namespace Yamagishi

namespace Paper908

open Real MeasureTheory Metric Yamagishi.Paper912

/-- ローレンツ因子 γ = 1/√(1 − β²)。 -/
noncomputable def γ (β : ℝ) : ℝ := 1 / √(1 - β ^ 2)

theorem γ_sq {β : ℝ} (hβ : β ^ 2 < 1) : γ β ^ 2 * (1 - β ^ 2) = 1 := by
  unfold γ
  rw [div_pow, one_pow, sq_sqrt (by linarith)]
  field_simp

theorem γ_pos {β : ℝ} (hβ : β ^ 2 < 1) : 0 < γ β := by
  unfold γ; have : 0 < √(1 - β ^ 2) := sqrt_pos.mpr (by linarith); positivity

/-- 静止の場のエネルギー U₀ = K/(8π)·∮ 1 dS。 -/
noncomputable def U0 (d : ℕ) (K : ℝ) : ℝ := K / (8 * π) * ∫ _ω, (1 : ℝ) ∂σ d

/-- 動く場のエネルギー U = K/(8πγ)·∮(n_i² + γ²(1 + β²)(1 − n_i²)) dS。 -/
noncomputable def U (d : ℕ) (i : Fin d) (K β : ℝ) : ℝ :=
  K / (8 * π * γ β) * ∫ ω, (((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 +
    γ β ^ 2 * (1 + β ^ 2) * (1 - ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2)) ∂σ d

/-- 動く場の運動量 p = βγK/(4π)·∮(1 − n_i²) dS。 -/
noncomputable def p (d : ℕ) (i : Fin d) (K β : ℝ) : ℝ :=
  β * γ β * K / (4 * π) * ∫ ω, (1 - ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2) ∂σ d

theorem integral_one (d : ℕ) (hd : 0 < d) : ∫ _ω, (1 : ℝ) ∂σ d = d * V d := by
  rw [integral_const, smul_eq_mul, mul_one, sigma_univ d hd]

theorem integral_sin_sq (d : ℕ) (i : Fin d) :
    ∫ ω, (1 - ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2) ∂σ d = (d - 1) * V d := by
  have hd : 0 < d := Fin.pos i
  rw [integral_sub (integrable_of_continuous _ continuous_const)
    (integrable_of_continuous _ (by fun_prop)), integral_one d hd, sphere_integral_coord_sq]
  ring

theorem V_pos (d : ℕ) : 0 < V d := by
  unfold V; exact div_pos (by positivity) (Gamma_pos_of_pos (by positivity))

/-- (1) 運動量 p = 2(1 − 1/d)γβU₀。 -/
theorem momentum_eq (d : ℕ) (i : Fin d) (K β : ℝ) :
    p d i K β = 2 * (1 - 1 / (d : ℝ)) * γ β * β * U0 d K := by
  have hd : 0 < d := Fin.pos i
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold p U0
  rw [integral_sin_sq, integral_one d hd]
  field_simp
  ring

/-- (1) エネルギー U = γU₀(1 + (1 − 2/d)β²)（すべての β² < 1 で厳密）。 -/
theorem energy_eq (d : ℕ) (i : Fin d) (K : ℝ) {β : ℝ} (hβ : β ^ 2 < 1) :
    U d i K β = γ β * U0 d K * (1 + (1 - 2 / (d : ℝ)) * β ^ 2) := by
  have hd : 0 < d := Fin.pos i
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hg := γ_sq hβ
  have hg0 := (γ_pos hβ).ne'
  unfold U U0
  rw [integral_add (integrable_of_continuous _ (by fun_prop))
    (integrable_of_continuous _ (by fun_prop)), integral_const_mul, integral_sin_sq,
    sphere_integral_coord_sq, integral_one d hd]
  have h2d : (d : ℝ) * (2 / d) = 2 := by field_simp
  have key : V d + γ β ^ 2 * (1 + β ^ 2) * ((d - 1) * V d) =
      γ β ^ 2 * (d * V d) * (1 + (1 - 2 / (d : ℝ)) * β ^ 2) := by
    linear_combination (-V d) * hg + (γ β ^ 2 * V d * β ^ 2) * h2d
  rw [key]
  field_simp

/-- (1) d = 3 で p = (4/3)γβU₀、U = γU₀(1 + β²/3)。 -/
theorem three_dim (i : Fin 3) (K : ℝ) {β : ℝ} (hβ : β ^ 2 < 1) :
    p 3 i K β = 4 / 3 * γ β * β * U0 3 K ∧ U 3 i K β = γ β * U0 3 K * (1 + β ^ 2 / 3) := by
  rw [momentum_eq, energy_eq 3 i K hβ]
  constructor <;> push_cast <;> ring

/-- (2) 0 < β < 1、U₀ ≠ 0 で、p/(γβ) = U/γ ⇔ d = 2（場だけで 4 元ベクトルになるのは d = 2 だけ）。 -/
theorem four_vector_iff (d : ℕ) (i : Fin d) (K : ℝ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hU : U0 d K ≠ 0) :
    p d i K β / (γ β * β) = U d i K β / γ β ↔ d = 2 := by
  have hβ : β ^ 2 < 1 := by nlinarith
  have hg0 := (γ_pos hβ).ne'
  have hd : 0 < d := Fin.pos i
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [momentum_eq, energy_eq d i K hβ]
  rw [show 2 * (1 - 1 / (d : ℝ)) * γ β * β * U0 d K / (γ β * β) = 2 * (1 - 1 / (d : ℝ)) * U0 d K by
    field_simp]
  rw [show γ β * U0 d K * (1 + (1 - 2 / (d : ℝ)) * β ^ 2) / γ β =
    U0 d K * (1 + (1 - 2 / (d : ℝ)) * β ^ 2) by field_simp]
  constructor
  · intro h
    have h1 : U0 d K * ((1 - 2 / (d : ℝ)) * (1 - β ^ 2)) = 0 := by linear_combination h
    have h2 : (1 - 2 / (d : ℝ)) * (1 - β ^ 2) = 0 := (mul_eq_zero.mp h1).resolve_left hU
    have h3 : 1 - 2 / (d : ℝ) = 0 := (mul_eq_zero.mp h2).resolve_right (by nlinarith)
    have : (d : ℝ) = 2 := by field_simp at h3; linarith
    exact_mod_cast this
  · rintro rfl
    push_cast
    ring

/-- (3) 原稿の計算 3.1 の形 p = β·2⟨sin²θ⟩·U（⟨sin²θ⟩ = 1 − 1/d、U は動く場のエネルギー）は、
d ≥ 2 では β = 0 か d = 2 のときに限って正しい。 -/
theorem paper_formula_iff (d : ℕ) (i : Fin d) (K : ℝ) {β : ℝ} (hβ : β ^ 2 < 1) (hd2 : 2 ≤ d)
    (hU : U0 d K ≠ 0) :
    p d i K β = β * (2 * (1 - 1 / (d : ℝ))) * U d i K β ↔ β = 0 ∨ d = 2 := by
  have hg0 := (γ_pos hβ).ne'
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (1 - 1 / (d : ℝ)) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have : 1 / (d : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    apply ne_of_gt
    linarith
  rw [momentum_eq, energy_eq d i K hβ]
  constructor
  · intro h
    have h1 : (2 * (1 - 1 / (d : ℝ)) * γ β * U0 d K) * (β * ((1 - 2 / (d : ℝ)) * β ^ 2)) = 0 := by
      linear_combination -h
    have hc : 2 * (1 - 1 / (d : ℝ)) * γ β * U0 d K ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd1) hg0) hU
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hc) with hb | h2
    · exact Or.inl hb
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · right
        have : (d : ℝ) = 2 := by field_simp at h3; linarith
        exact_mod_cast this
      · left; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  · rintro (rfl | rfl)
    · ring
    · push_cast; ring

/-! ### 球の体積の係数との比べ -/

/-- 球の体積の係数 c_d = V_d/π^⌊d/2⌋。 -/
noncomputable def ballCoeff (d : ℕ) : ℝ := V d / π ^ (d / 2)

theorem ballCoeff_succ_succ (d : ℕ) : ballCoeff (d + 2) = 2 / (d + 2) * ballCoeff d := by
  unfold ballCoeff
  rw [V_succ_succ, show (d + 2) / 2 = d / 2 + 1 by omega, pow_succ]
  have : π ≠ 0 := pi_ne_zero
  field_simp

theorem ballCoeff_two : ballCoeff 2 = 1 := by
  unfold ballCoeff; rw [V_two]; simp [pi_ne_zero]

theorem ballCoeff_three : ballCoeff 3 = 4 / 3 := by
  unfold ballCoeff; rw [V_three]; norm_num; field_simp

theorem ballCoeff_le (d : ℕ) (hd : 4 ≤ d) : ballCoeff d ≤ 8 / 15 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 6 with h | h
    · interval_cases d
      · rw [show (4 : ℕ) = 2 + 2 by rfl, ballCoeff_succ_succ, ballCoeff_two]; norm_num
      · rw [show (5 : ℕ) = 3 + 2 by rfl, ballCoeff_succ_succ, ballCoeff_three]; norm_num
    · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
      rw [ballCoeff_succ_succ]
      have h1 := ih e (by omega) (by omega)
      have h2 : 0 ≤ ballCoeff e := by
        unfold ballCoeff; exact div_nonneg (V_pos e).le (by positivity)
      have h3 : (2 : ℝ) / (e + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith

/-- (4) d ≥ 2 で、球の体積の係数が 2(1 − 1/d) に等しい ⇔ d = 2 か 3。 -/
theorem ball_coeff_eq_iff (d : ℕ) (hd : 2 ≤ d) :
    ballCoeff d = 2 * (1 - 1 / (d : ℝ)) ↔ d = 2 ∨ d = 3 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h4 : 4 ≤ d := by omega
    have := ballCoeff_le d h4
    have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast h4
    have : 1 / (d : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hd4
    linarith
  · rintro (rfl | rfl)
    · rw [ballCoeff_two]; norm_num
    · rw [ballCoeff_three]; norm_num

end Paper908

end Yamagishi
