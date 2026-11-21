/-
論文236『同じ「＝0」でも、解の集まりは五つの別の種類のものである』の格上げ（一般の形）。

原稿（236_yamagishi_five_solution_sets/…_jp.tex）は、同じ「＝0」が住む場所によって別の集まりを返す
ことを、六つの場所で数えている。芯は第 6 節で、J[y] = ∫₀^L (y′² − y²)dx、y(0) = y(L) = 0 に
y = sin(πx/L) を入れた値を L = 1, 2, 3, π, 3.5, 4, 10 で測り、閉じた形 (L/2)((π/L)² − 1) と照合して
「L > π では y ≡ 0 は最小点ではなく鞍点」と述べる。L ≤ π で最小であることは示していない。
第 3 節は x² + 1 = 0 を法 p（p = 3〜29 の奇素数）で解き、観察 7.1 の表で「有限体では 0 個か 2 個」と
まとめる。第 4 節は実 2×2 行列の X² = I の解として、b ≠ 0 の族 (a, b; (1 − a²)/b, −a) を挙げる。

ここで証明した言明：
  (1) `J_sin`：すべての L > 0 と自然数 k ≥ 1 で J[sin(kπx/L)] = (L/2)((kπ/L)² − 1)。
  (2) `J_nonneg_of_lt_pi`・`J_nonneg_of_le_pi`：L ≤ π なら、y(0) = y(L) = 0 のどの C¹ 関数でも J[y] ≥ 0。
      （L < π は J[y] = ∫(y′ − y cot(x + a))²、a = (π − L)/2 と書けることから。L = π は尺度の変換で
      L < π に戻して極限をとる。）
  (3) `zero_is_min_iff`：L > 0 で、y ≡ 0 が J の最小点 ⇔ L ≤ π。`J_takes_pos`：どの L でも J は正の値を
      とる。したがって L > π では y ≡ 0 は鞍点（正にも負にもなる）。
  (4) `card_roots_char_ne_two`・`card_roots_char_two`：有限体 F で x² + 1 = 0 の解の数は、標数が 2 で
      なければ 0 か 2、標数 2 なら 1（x = 1 だけ）。`card_roots_zmod_two`：法 2 では 1 個。
      `roots_two_iff_zmod`：奇素数 p で 2 個 ⇔ p mod 4 ≠ 3。
  (5) `sq_eq_one_iff`：実 2×2 行列で X² = I ⇔ X = I か X = −I か（d = −a かつ a² + bc = 1）。
      `manuscript_family`：原稿の b ≠ 0 の族は解。`missing_family`：(1, 0; c, −1) は解で、±I でも
      原稿の族でもない（b = 0 の解の書き落とし）。
形式化していないもの：L < π での狭義の最小（J[y] = 0 なら y ≡ 0）、四元数の球面、微分方程式の解空間、
分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper236

open Real Set Filter Topology intervalIntegral

/-! ### 汎関数 J -/

/-- J[y] = ∫₀^L (y′² − y²)。 -/
noncomputable def J (L : ℝ) (y : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..L, (deriv y x ^ 2 - y x ^ 2)

/-- (1) 閉じた形（k ≥ 1）。 -/
theorem J_sin {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 0 < k) :
    J L (fun x => sin (k * π / L * x)) = L / 2 * ((k * π / L) ^ 2 - 1) := by
  set ω := (k : ℝ) * π / L with hω
  have hωpos : 0 < ω := by
    rw [hω]; have : (0 : ℝ) < k := by exact_mod_cast hk
    exact div_pos (mul_pos this pi_pos) hL
  have hd : ∀ x, deriv (fun x => sin (ω * x)) x = ω * cos (ω * x) := by
    intro x
    have h := ((hasDerivAt_id x).const_mul ω).sin
    simp only [id, mul_one] at h
    rw [h.deriv]; ring
  have hωL : ω * L = k * π := by rw [hω]; field_simp
  unfold J
  simp_rw [hd]
  have hc : ∫ x in (0 : ℝ)..L, cos (ω * x) ^ 2 = L / 2 := by
    rw [integral_comp_mul_left (fun x => cos x ^ 2) hωpos.ne', integral_cos_sq, hωL]
    simp [sin_nat_mul_pi]
    rw [hω]; field_simp
  have hs : ∫ x in (0 : ℝ)..L, sin (ω * x) ^ 2 = L / 2 := by
    rw [integral_comp_mul_left (fun x => sin x ^ 2) hωpos.ne', integral_sin_sq, hωL]
    simp [sin_nat_mul_pi]
    rw [hω]; field_simp
  rw [intervalIntegral.integral_sub,
    show (fun x => (ω * cos (ω * x)) ^ 2) = fun x => ω ^ 2 * cos (ω * x) ^ 2 by
      funext x; ring, integral_const_mul, hc, hs]
  · ring
  · exact (by fun_prop : Continuous fun x => (ω * cos (ω * x)) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x => sin (ω * x) ^ 2).intervalIntegrable _ _

/-- cot(x + a)。 -/
noncomputable def cotA (a x : ℝ) : ℝ := cos (x + a) / sin (x + a)

/-- G = y² cot(x + a)。 -/
noncomputable def Gf (y : ℝ → ℝ) (a x : ℝ) : ℝ := (y x * y x) * cotA a x

/-- G の導関数。 -/
noncomputable def G'f (y y' : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (y' x * y x + y x * y' x) * cotA a x +
    (y x * y x) * ((-sin (x + a) * sin (x + a) - cos (x + a) * cos (x + a)) / sin (x + a) ^ 2)

/-- 平方の項 (y′ − y cot(x + a))²。 -/
noncomputable def Qf (y y' : ℝ → ℝ) (a x : ℝ) : ℝ := (y' x - y x * cotA a x) ^ 2

theorem hasDerivAt_Gf {y y' : ℝ → ℝ} {a x : ℝ} (hy : HasDerivAt y (y' x) x)
    (hs : sin (x + a) ≠ 0) : HasDerivAt (Gf y a) (G'f y y' a x) x := by
  have hsa : HasDerivAt (fun x => sin (x + a)) (cos (x + a)) x := by
    have := ((hasDerivAt_id' x).add_const a).sin; simpa using this
  have hca : HasDerivAt (fun x => cos (x + a)) (-sin (x + a)) x := by
    have := ((hasDerivAt_id' x).add_const a).cos; simpa using this
  exact (hy.mul hy).mul (hca.div hsa hs)

theorem continuousOn_cotA {a : ℝ} {D : Set ℝ} (hs : ∀ x ∈ D, sin (x + a) ≠ 0) :
    ContinuousOn (cotA a) D :=
  (by fun_prop : Continuous fun x => cos (x + a)).continuousOn.div
    (by fun_prop : Continuous fun x => sin (x + a)).continuousOn hs

theorem integrand_eq {y y' : ℝ → ℝ} {a x : ℝ} (hs : sin (x + a) ≠ 0) :
    y' x ^ 2 - y x ^ 2 = Qf y y' a x + G'f y y' a x := by
  simp only [Qf, G'f, cotA]
  field_simp
  ring

/-- (2) L < π なら J[y] ≥ 0。 -/
theorem J_nonneg_of_lt_pi {L : ℝ} (hL : 0 < L) (hLπ : L < π) {y : ℝ → ℝ} (hy : ContDiff ℝ 1 y)
    (h0 : y 0 = 0) (hL0 : y L = 0) : 0 ≤ J L y := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (π - L) / 2 := ⟨_, rfl⟩
  have hyd : ∀ x, HasDerivAt y (deriv y x) x :=
    fun x => ((hy.differentiable one_ne_zero) x).hasDerivAt
  have hy'c : Continuous (deriv y) := hy.continuous_deriv le_rfl
  have hyc : Continuous y := hy.continuous
  have hsne : ∀ x ∈ Icc 0 L, sin (x + a) ≠ 0 := by
    intro x hx
    apply ne_of_gt
    apply sin_pos_of_pos_of_lt_pi
    · rw [ha]; linarith [hx.1]
    · rw [ha]; linarith [hx.2]
  have hcot := continuousOn_cotA hsne
  have hcontQ : ContinuousOn (Qf y (deriv y) a) (Icc 0 L) := by
    have h1 : ContinuousOn (fun x => y x * cotA a x) (Icc 0 L) := hyc.continuousOn.mul hcot
    have h2 : ContinuousOn (fun x => deriv y x - y x * cotA a x) (Icc 0 L) :=
      hy'c.continuousOn.sub h1
    exact h2.pow 2
  have hcontG' : ContinuousOn (G'f y (deriv y) a) (Icc 0 L) := by
    have h1 : Continuous (fun x => deriv y x * y x + y x * deriv y x) :=
      (hy'c.mul hyc).add (hyc.mul hy'c)
    have h2 : ContinuousOn (fun x => (deriv y x * y x + y x * deriv y x) * cotA a x) (Icc 0 L) :=
      h1.continuousOn.mul hcot
    have h3 : ContinuousOn (fun x => (-sin (x + a) * sin (x + a) - cos (x + a) * cos (x + a)) /
        sin (x + a) ^ 2) (Icc 0 L) :=
      (by fun_prop : Continuous fun x =>
        -sin (x + a) * sin (x + a) - cos (x + a) * cos (x + a)).continuousOn.div
        (by fun_prop : Continuous fun x => sin (x + a) ^ 2).continuousOn
        (fun x hx => pow_ne_zero 2 (hsne x hx))
    have h4 : ContinuousOn (fun x => (y x * y x) * ((-sin (x + a) * sin (x + a) -
        cos (x + a) * cos (x + a)) / sin (x + a) ^ 2)) (Icc 0 L) :=
      (hyc.mul hyc).continuousOn.mul h3
    exact h2.add h4
  have hI : uIcc 0 L = Icc 0 L := uIcc_of_le hL.le
  have hQi : IntervalIntegrable (Qf y (deriv y) a) MeasureTheory.volume 0 L :=
    (hcontQ.mono (by rw [hI])).intervalIntegrable
  have hG'i : IntervalIntegrable (G'f y (deriv y) a) MeasureTheory.volume 0 L :=
    (hcontG'.mono (by rw [hI])).intervalIntegrable
  have heq : EqOn (fun x => deriv y x ^ 2 - y x ^ 2)
      (fun x => Qf y (deriv y) a x + G'f y (deriv y) a x) (uIcc 0 L) := by
    intro x hx
    rw [hI] at hx
    exact integrand_eq (hsne x hx)
  have hFTC : ∫ x in (0 : ℝ)..L, G'f y (deriv y) a x = Gf y a L - Gf y a 0 :=
    integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_Gf (hyd x) (hsne x (by rwa [hI] at hx))) hG'i
  have hGL : Gf y a L = 0 := by simp [Gf, hL0]
  have hG0 : Gf y a 0 = 0 := by simp [Gf, h0]
  unfold J
  rw [integral_congr heq, integral_add hQi hG'i, hFTC, hGL, hG0, sub_zero, add_zero]
  exact integral_nonneg hL.le (fun x _ => sq_nonneg _)

/-- 尺度の変換：z(x) = y(rx) の J。 -/
theorem J_scale {r : ℝ} (hr : 0 < r) {y : ℝ → ℝ} (hy : ContDiff ℝ 1 y) (L : ℝ) :
    J (L / r) (fun x => y (r * x)) =
      r⁻¹ * (r ^ 2 * ∫ x in (0 : ℝ)..L, deriv y x ^ 2) - r⁻¹ * ∫ x in (0 : ℝ)..L, y x ^ 2 := by
  have hd : ∀ x, deriv (fun x => y (r * x)) x = r * deriv y (r * x) := by
    intro x
    have h1 := ((hy.differentiable one_ne_zero) (r * x)).hasDerivAt
    have h2 := h1.comp x ((hasDerivAt_id x).const_mul r)
    simp only [mul_one] at h2
    rw [show (fun x => y (r * x)) = y ∘ fun x => r * x from rfl, h2.deriv]; ring
  have hy'c : Continuous (deriv y) := hy.continuous_deriv le_rfl
  have hyc : Continuous y := hy.continuous
  unfold J
  simp_rw [hd]
  rw [intervalIntegral.integral_sub]
  · rw [show (fun x => (r * deriv y (r * x)) ^ 2) = fun x => r ^ 2 * deriv y (r * x) ^ 2 by
      funext x; ring, integral_const_mul,
      integral_comp_mul_left (fun x => deriv y x ^ 2) hr.ne',
      integral_comp_mul_left (fun x => y x ^ 2) hr.ne']
    simp only [mul_zero, smul_eq_mul]
    rw [show r * (L / r) = L by field_simp]
    ring
  · exact (by fun_prop : Continuous fun x => (r * deriv y (r * x)) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x => y (r * x) ^ 2).intervalIntegrable _ _

/-- (2) L ≤ π なら J[y] ≥ 0。 -/
theorem J_nonneg_of_le_pi {L : ℝ} (hL : 0 < L) (hLπ : L ≤ π) {y : ℝ → ℝ} (hy : ContDiff ℝ 1 y)
    (h0 : y 0 = 0) (hL0 : y L = 0) : 0 ≤ J L y := by
  rcases lt_or_eq_of_le hLπ with h | h
  · exact J_nonneg_of_lt_pi hL h hy h0 hL0
  subst h
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ x in (0 : ℝ)..π, deriv y x ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∫ x in (0 : ℝ)..π, y x ^ 2 := ⟨_, rfl⟩
  -- r > 1 で r²A ≥ B
  have hr : ∀ r : ℝ, 1 < r → B ≤ r ^ 2 * A := by
    intro r hr1
    have hrpos : 0 < r := by linarith
    have hz : ContDiff ℝ 1 (fun x => y (r * x)) := hy.comp (by fun_prop)
    have hpos : 0 < π / r := div_pos pi_pos hrpos
    have hlt : π / r < π := by rw [div_lt_iff₀ hrpos]; nlinarith [pi_pos]
    have := J_nonneg_of_lt_pi hpos hlt hz (show y (r * 0) = 0 by rw [mul_zero]; exact h0) (by
      rw [show r * (π / r) = π by field_simp]; exact hL0)
    rw [J_scale hrpos hy π, ← hA, ← hB] at this
    have hinv : 0 < r⁻¹ := inv_pos.2 hrpos
    nlinarith
  have hT : Tendsto (fun r : ℝ => r ^ 2 * A) (𝓝[>] 1) (𝓝 A) := by
    have : Tendsto (fun r : ℝ => r ^ 2 * A) (𝓝 1) (𝓝 (1 ^ 2 * A)) :=
      ((continuous_pow 2).mul continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have hBA : B ≤ A := ge_of_tendsto hT (by
    filter_upwards [self_mem_nhdsWithin] with r hr1 using hr r hr1)
  unfold J
  rw [intervalIntegral.integral_sub, ← hA, ← hB]
  · linarith
  · exact ((hy.continuous_deriv le_rfl).pow 2).intervalIntegrable _ _
  · exact (hy.continuous.pow 2).intervalIntegrable _ _

theorem sin_contDiff (ω : ℝ) : ContDiff ℝ 1 (fun x => sin (ω * x)) := by fun_prop

/-- (3) y ≡ 0 が最小点 ⇔ L ≤ π。 -/
theorem zero_is_min_iff {L : ℝ} (hL : 0 < L) :
    (∀ y : ℝ → ℝ, ContDiff ℝ 1 y → y 0 = 0 → y L = 0 → 0 ≤ J L y) ↔ L ≤ π := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := h (fun x => sin ((1 : ℕ) * π / L * x)) (sin_contDiff _)
      (show sin ((1 : ℕ) * π / L * 0) = 0 by rw [mul_zero, sin_zero])
      (show sin ((1 : ℕ) * π / L * L) = 0 by
        rw [show ((1 : ℕ) : ℝ) * π / L * L = π by rw [Nat.cast_one, one_mul]; field_simp]
        exact sin_pi)
    rw [J_sin hL one_pos] at this
    have h1 : ((1 : ℕ) * π / L) ^ 2 < 1 := by
      rw [Nat.cast_one, one_mul, div_pow, div_lt_one (by positivity)]
      nlinarith [pi_pos]
    nlinarith
  · intro hLπ y hy h0 hL0
    exact J_nonneg_of_le_pi hL hLπ hy h0 hL0

/-- (3) どの L でも J は正の値をとる（y ≡ 0 は決して最大点でない）。 -/
theorem J_takes_pos {L : ℝ} (hL : 0 < L) :
    ∃ y : ℝ → ℝ, ContDiff ℝ 1 y ∧ y 0 = 0 ∧ y L = 0 ∧ 0 < J L y := by
  obtain ⟨k, hk⟩ := exists_nat_gt (L / π)
  have hk0 : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (div_pos hL pi_pos) hk
    exact_mod_cast this
  refine ⟨fun x => sin (k * π / L * x), sin_contDiff _, by simp only [mul_zero, sin_zero], ?_, ?_⟩
  · show sin (k * π / L * L) = 0
    rw [show (k : ℝ) * π / L * L = k * π by field_simp]; exact sin_nat_mul_pi k
  · rw [J_sin hL hk0]
    have hπ := pi_pos
    have h1 : 1 < ((k : ℝ) * π / L) ^ 2 := by
      have : 1 < (k : ℝ) * π / L := by
        rw [div_lt_iff₀ hπ] at hk; rw [one_lt_div hL]; linarith
      nlinarith
    nlinarith

/-! ### 有限体での x² + 1 = 0 -/

section FiniteField

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- x² + 1 = 0 の解の集まり。 -/
def roots : Finset F := (Finset.univ : Finset F).filter (fun x => x ^ 2 + 1 = 0)

variable {F}

theorem roots_eq_pair {a : F} (ha : a ^ 2 + 1 = 0) : roots F = {a, -a} := by
  ext x
  simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hx
    have : (x - a) * (x + a) = 0 := by linear_combination hx - ha
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rintro (rfl | rfl)
    · exact ha
    · linear_combination ha

/-- (4) 標数が 2 でなければ、解の数は 0 か 2。 -/
theorem card_roots_char_ne_two (h : ringChar F ≠ 2) :
    (roots F).card = 0 ∨ (roots F).card = 2 := by
  by_cases hex : ∃ a : F, a ^ 2 + 1 = 0
  · obtain ⟨a, ha⟩ := hex
    right
    rw [roots_eq_pair ha, Finset.card_pair]
    intro hne
    have ha0 : a = 0 := (Ring.eq_self_iff_eq_zero_of_char_ne_two h).1 hne.symm
    rw [ha0] at ha; simp at ha
  · left
    rw [Finset.card_eq_zero, roots, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hex ⟨x, hx⟩

/-- (4) 標数 2 なら、解はちょうど一つ（x = 1）。 -/
theorem card_roots_char_two (h : ringChar F = 2) : (roots F).card = 1 := by
  have : CharP F 2 := ringChar.of_eq h
  have h1 : (1 : F) ^ 2 + 1 = 0 := by rw [one_pow]; exact CharTwo.add_self_eq_zero 1
  rw [roots_eq_pair h1, CharTwo.neg_eq]
  simp

end FiniteField

/-- (4) 法 2 では解は一つ（原稿の「0 個か 2 個」が崩れる）。 -/
theorem card_roots_zmod_two : (roots (ZMod 2)).card = 1 := by decide

/-- (4) 奇素数 p で解が 2 個 ⇔ p mod 4 ≠ 3。 -/
theorem roots_two_iff_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (roots (ZMod p)).card = 2 ↔ p % 4 ≠ 3 := by
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  rw [← ZMod.exists_sq_eq_neg_one_iff]
  constructor
  · intro h2
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < (roots (ZMod p)).card)
    simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨a, by linear_combination -ha⟩
  · rintro ⟨a, ha⟩
    have ha' : a ^ 2 + 1 = 0 := by linear_combination -ha
    rcases card_roots_char_ne_two hc with h | h
    · exfalso
      rw [Finset.card_eq_zero] at h
      have : a ∈ roots (ZMod p) := by simp [roots, ha']
      rw [h] at this; simp at this
    · exact h

/-! ### 実 2×2 行列の X² = I -/

theorem mat_eq (a b c d a' b' c' d' : ℝ) :
    !![a, b; c, d] = !![a', b'; c', d'] ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun (congrFun h 0) 0, by simpa using congrFun (congrFun h 0) 1,
      by simpa using congrFun (congrFun h 1) 0, by simpa using congrFun (congrFun h 1) 1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

theorem neg_one_fin_two : -(1 : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, -1] := by
  rw [Matrix.one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- (5) X² = I の解の全体。 -/
theorem sq_eq_one_iff (a b c d : ℝ) :
    !![a, b; c, d] * !![a, b; c, d] = 1 ↔
      (!![a, b; c, d] = 1 ∨ !![a, b; c, d] = -1 ∨ (d = -a ∧ a ^ 2 + b * c = 1)) := by
  rw [neg_one_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two, mat_eq, mat_eq, mat_eq]
  constructor
  · rintro ⟨h11, h12, h21, h22⟩
    by_cases hs : d = -a
    · right; right; exact ⟨hs, by nlinarith⟩
    · have hs' : a + d ≠ 0 := fun h => hs (by linarith)
      have hb : b = 0 := by
        have : b * (a + d) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hs'
      have hc : c = 0 := by
        have : c * (a + d) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hs'
      subst hb hc
      have ha : a = 1 ∨ a = -1 := by
        have : (a - 1) * (a + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      have hd : d = 1 ∨ d = -1 := by
        have : (d - 1) * (d + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      rcases ha with ha | ha <;> rcases hd with hd | hd <;> subst ha hd
      · left; norm_num
      · exact absurd (by norm_num) hs
      · exact absurd (by norm_num) hs
      · right; left; norm_num
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, h⟩)
    · norm_num
    · norm_num
    · refine ⟨by linarith, by ring, by ring, by nlinarith⟩

/-- 原稿の族 (a, b; (1 − a²)/b, −a)。 -/
noncomputable def famX (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; (1 - a ^ 2) / b, -a]

/-- (5) 原稿の族は（b ≠ 0 で）解。 -/
theorem manuscript_family {a b : ℝ} (hb : b ≠ 0) : famX a b * famX a b = 1 := by
  unfold famX
  rw [sq_eq_one_iff]
  right; right
  refine ⟨rfl, ?_⟩
  field_simp
  ring

/-- (5) 書き落とし：(1, 0; c, −1) は解で、±I でも原稿の族でもない。 -/
theorem missing_family (c : ℝ) :
    !![1, 0; c, -1] * !![(1 : ℝ), 0; c, -1] = 1 ∧ !![(1 : ℝ), 0; c, -1] ≠ 1 ∧
      !![(1 : ℝ), 0; c, -1] ≠ -1 ∧ ∀ a b : ℝ, b ≠ 0 → !![(1 : ℝ), 0; c, -1] ≠ famX a b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sq_eq_one_iff]; right; right; norm_num
  · intro h
    rw [Matrix.one_fin_two, mat_eq] at h
    norm_num at h
  · intro h
    rw [neg_one_fin_two, mat_eq] at h
    norm_num at h
  · intro a b hb h
    rw [famX, mat_eq] at h
    exact hb h.2.1.symm

end Paper236

end Yamagishi
