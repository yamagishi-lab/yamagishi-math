/-
論文963『三つの誤差に相関があると材積の誤差は動き、いちばん効くのは形の係数と樹高の組である』の
格上げ（一般の形）。

原稿（963_yamagishi_correlated_errors_in_tree_volume_and_the_triangle_of_contributions/…_jp.tex）は、
三つの寄与 a_D = 0.04・a_h = 0.05・a_f = 0.08 で、一次の式
  (σ_V/V)² ≈ Σ a_i² + 2 Σ_{i<j} ρ_ij a_i a_j
が三つの相関を選ぶと 0 になること（三つが三角形をつくれるから）、寄与 0.02・0.05・0.08 では
1441×1441 の総当たりの最小が 0.010000（= 0.08 − 0.05 − 0.02）であることを、具体例で示している。

ここで証明した言明（寄与の数 k は任意、寄与 a_i ≥ 0、相関の行列 ρ は半正定値で対角が 1）：
  一次の式 Q(ρ, a) = Σ_{i,j} a_i ρ_ij a_j について、a_j が最大の寄与のとき
  (1) `Q_lower`：すべての相関の行列で Q ≥ (max(0, 2a_j − Σa))²（j は最大でなくても成り立つ）。
  (2) `Q_attain`：等号を与える相関の行列が在る。よって `Q_isLeast`：最小値はちょうど
      (max(0, 2a_max − Σa))²。相対誤差（その平方根）の最小は max(0, 2a_max − Σa)。
  (3) `Q_zero_iff`：一次の式を 0 にできる ⇔ 最大の寄与が残りの寄与の和以下（多角形の不等式。
      k = 3 なら三角形の条件）。
定義に置いたもの：相関の行列（半正定値・対角 1）と一次の式。誤差の伝播の一次の式そのものは原稿の
式で、正規分布としたときの正確な値（0 にならない）は扱わない。冪が負の量は、寄与を絶対値で数える
（a_i ≥ 0 の仮定）。
証明の筋：(1) は x = a − b·e_j（b = (ρa)_j）に半正定値を使って Q ≥ b²、さらに ρ_ji ≥ −1 から
b ≥ 2a_j − Σa。(2) は、2a_j ≥ Σa なら符号のベクトル τ（j で +1、ほかで −1）の ρ = ττᵀ、
2a_j < Σa なら、残りを貪欲に ± に分けて差を a_j 以下にし、平面の三角形を作って和を 0 にする
（ρ_ik = c_i c_k + s_i s_k、(c_i, s_i) は単位ベクトル）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper963

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- 相関の行列：半正定値で、対角がすべて 1。 -/
def IsCorr (ρ : Matrix ι ι ℝ) : Prop := ρ.PosSemidef ∧ ∀ i, ρ i i = 1

/-- 一次の式 Σ_{i,j} a_i ρ_ij a_j（相対誤差の二乗の一次の近似）。 -/
def Q (ρ : Matrix ι ι ℝ) (a : ι → ℝ) : ℝ := ∑ i, ∑ k, a i * ρ i k * a k

theorem Q_eq_dot (ρ : Matrix ι ι ℝ) (a : ι → ℝ) : Q ρ a = star a ⬝ᵥ (ρ *ᵥ a) := by
  simp [Q, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem Q_nonneg {ρ : Matrix ι ι ℝ} (h : ρ.PosSemidef) (x : ι → ℝ) : 0 ≤ Q ρ x := by
  rw [Q_eq_dot]; exact h.dotProduct_mulVec_nonneg x

theorem symm_of_psd {ρ : Matrix ι ι ℝ} (h : ρ.PosSemidef) (i k : ι) : ρ i k = ρ k i := by
  have := h.1.apply k i
  simpa using this

/-- 相関は −1 以上。 -/
theorem corr_ge_neg_one {ρ : Matrix ι ι ℝ} (h : IsCorr ρ) (j i : ι) : -1 ≤ ρ j i := by
  by_cases hji : j = i
  · subst hji; rw [h.2]; norm_num
  have := Q_nonneg h.1 (Pi.single j 1 + Pi.single i 1)
  simp only [Q, Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib,
    ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  rw [h.2 j, h.2 i, symm_of_psd h.1 i j] at this
  linarith

/-- (1) 下からの評価：どの j についても Q ≥ (max(0, 2a_j − Σa))²。 -/
theorem Q_lower {ρ : Matrix ι ι ℝ} (h : IsCorr ρ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (j : ι) :
    (max 0 (2 * a j - ∑ i, a i)) ^ 2 ≤ Q ρ a := by
  set b := ∑ k, ρ j k * a k with hb
  -- Q(a − b e_j) = Q(a) − b²
  have hT : ρᵀ = ρ := by ext i k; exact symm_of_psd h.1 k i
  have hx := h.1.dotProduct_mulVec_nonneg (a - b • Pi.single j 1)
  have hbm : (ρ *ᵥ a) j = b := rfl
  have hba : a ⬝ᵥ ρ j = b := by rw [dotProduct_comm]; rfl
  have hcol : a ⬝ᵥ ρ.col j = b := by
    rw [← hba]; congr 1; ext i; exact symm_of_psd h.1 i j
  have hcj : ρ.col j j = 1 := h.2 j
  simp only [star_trivial, mulVec_sub, mulVec_smul, mulVec_single_one, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, single_one_dotProduct, smul_eq_mul,
    hbm, hcol, hcj] at hx
  rw [Q_eq_dot, star_trivial]
  -- b + Σa ≥ 2a_j
  have hb2 : 2 * a j - ∑ i, a i ≤ b := by
    have hsum : b + ∑ i, a i = ∑ i, (ρ j i + 1) * a i := by
      rw [hb, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hterm : (ρ j j + 1) * a j ≤ ∑ i, (ρ j i + 1) * a i :=
      Finset.single_le_sum (f := fun i => (ρ j i + 1) * a i)
        (fun i _ => mul_nonneg (by linarith [corr_ge_neg_one h j i]) (ha i)) (Finset.mem_univ j)
    rw [h.2 j] at hterm
    linarith
  have hQ0 : 0 ≤ a ⬝ᵥ (ρ *ᵥ a) := by simpa [Q_eq_dot] using Q_nonneg h.1 a
  rcases le_total (2 * a j - ∑ i, a i) 0 with hle | hle
  · rw [max_eq_left hle]; simpa using hQ0
  · rw [max_eq_right hle]
    nlinarith

/-! ## 等号を与える相関の行列 -/

/-- 二つの実ベクトル c, s から作る行列 ρ_ik = c_i c_k + s_i s_k。 -/
def corrOf (c s : ι → ℝ) : Matrix ι ι ℝ := fun i k => c i * c k + s i * s k

theorem Q_corrOf (c s x : ι → ℝ) :
    Q (corrOf c s) x = (∑ i, x i * c i) ^ 2 + (∑ i, x i * s i) ^ 2 := by
  simp only [Q, corrOf, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

theorem corrOf_isCorr (c s : ι → ℝ) (hu : ∀ i, c i ^ 2 + s i ^ 2 = 1) : IsCorr (corrOf c s) := by
  refine ⟨PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_, ?_⟩
  · ext i k; simp [corrOf, conjTranspose_apply]; ring
  · intro x
    rw [← Q_eq_dot, Q_corrOf]; positivity
  · intro i; simp only [corrOf]; nlinarith [hu i]

/-- 貪欲に符号を選ぶ：0 ≤ a_i ≤ M なら、符号 σ_i = ±1 で |Σ σ_i a_i| ≤ M にできる。 -/
theorem greedy_signs (a : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (T : Finset ι)
    (hT : ∀ i ∈ T, 0 ≤ a i ∧ a i ≤ M) :
    ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ |∑ i ∈ T, σ i * a i| ≤ M := by
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simpa using hM⟩
  | insert x T hx ih =>
    obtain ⟨σ, hσ, hD⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨hx0, hxM⟩ := hT x (Finset.mem_insert_self x T)
    set D := ∑ i ∈ T, σ i * a i
    have hrest : ∀ t : ℝ, ∑ i ∈ T, (Function.update σ x t) i * a i = D := fun t =>
      Finset.sum_congr rfl (fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact hx hi)])
    by_cases hD0 : 0 ≤ D
    · refine ⟨Function.update σ x (-1), ?_, ?_⟩
      · intro i; by_cases hi : i = x
        · subst hi; simp
        · rw [Function.update_of_ne hi]; exact hσ i
      · rw [Finset.sum_insert hx, hrest, Function.update_self]
        rw [abs_le] at hD ⊢; constructor <;> linarith
    · refine ⟨Function.update σ x 1, ?_, ?_⟩
      · intro i; by_cases hi : i = x
        · subst hi; simp
        · rw [Function.update_of_ne hi]; exact hσ i
      · rw [Finset.sum_insert hx, hrest, Function.update_self]
        rw [abs_le] at hD ⊢; constructor <;> linarith

/-- 三辺 A, B, m が三角形の条件 |A − B| ≤ m ≤ A + B を満たせば、単位ベクトル (wc, ws) で
(A + B·wc)² + (B·ws)² = m² にできる。 -/
theorem triangle_closes (A B m : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : 0 ≤ m)
    (h1 : |A - B| ≤ m) (h2 : m ≤ A + B) :
    ∃ wc ws : ℝ, wc ^ 2 + ws ^ 2 = 1 ∧ (A + B * wc) ^ 2 + (B * ws) ^ 2 = m ^ 2 := by
  rw [abs_le] at h1
  obtain ⟨h1a, h1b⟩ := h1
  by_cases hAB : A * B = 0
  · refine ⟨1, 0, by norm_num, ?_⟩
    rcases mul_eq_zero.mp hAB with h | h <;> subst h <;> nlinarith
  · have hAB' : 0 < A * B := lt_of_le_of_ne (mul_nonneg hA hB) (Ne.symm hAB)
    set wc := (m ^ 2 - A ^ 2 - B ^ 2) / (2 * (A * B)) with hwc
    have hlo : -1 ≤ wc := by
      rw [hwc, le_div_iff₀ (by positivity)]; nlinarith
    have hhi : wc ≤ 1 := by
      rw [hwc, div_le_iff₀ (by positivity)]; nlinarith
    have hw2 : wc ^ 2 ≤ 1 := by nlinarith
    refine ⟨wc, √(1 - wc ^ 2), ?_, ?_⟩
    · rw [Real.sq_sqrt (by linarith)]; ring
    · rw [mul_pow, Real.sq_sqrt (by linarith)]
      have : 2 * (A * B) * wc = m ^ 2 - A ^ 2 - B ^ 2 := by
        rw [hwc]; field_simp; exact mul_div_cancel_left₀ _ hAB
      nlinarith

/-- (2) 等号を与える相関の行列が在る（a_j が最大の寄与のとき）。 -/
theorem Q_attain {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (j : ι) (hj : ∀ i, a i ≤ a j) :
    ∃ ρ, IsCorr ρ ∧ Q ρ a = (max 0 (2 * a j - ∑ i, a i)) ^ 2 := by
  have hsplit : ∑ i, a i = a j + ∑ i ∈ univ.erase j, a i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  rcases le_total 0 (2 * a j - ∑ i, a i) with hle | hle
  · -- 符号のベクトル τ（j で +1、ほかで −1）
    refine ⟨corrOf (fun i => if i = j then 1 else -1) 0, corrOf_isCorr _ _ (fun i => by
      split_ifs <;> norm_num), ?_⟩
    have : ∑ i, a i * (if i = j then (1 : ℝ) else -1) = 2 * a j - ∑ i, a i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hsplit]
      simp only [ite_true]
      have : ∑ i ∈ univ.erase j, a i * (if i = j then (1 : ℝ) else -1) =
          -∑ i ∈ univ.erase j, a i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i hi => by
          simp [Finset.ne_of_mem_erase hi])
      rw [this]; ring
    rw [Q_corrOf, max_eq_right hle, this]; simp
  · rw [max_eq_left hle]
    by_cases haj : a j = 0
    · -- すべての寄与が 0
      have h0 : ∀ i, a i = 0 := fun i => le_antisymm (haj ▸ hj i) (ha i)
      refine ⟨corrOf 1 0, corrOf_isCorr _ _ (fun i => by simp), ?_⟩
      rw [Q_corrOf]; simp [h0]
    have hajpos : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm haj)
    set T := univ.erase j
    set R := ∑ i ∈ T, a i with hR
    obtain ⟨σ, hσ, hD⟩ := greedy_signs a (a j) (ha j) T (fun i _ => ⟨ha i, hj i⟩)
    set D := ∑ i ∈ T, σ i * a i with hDdef
    set A := (R + D) / 2 with hAdef
    set B := (R - D) / 2 with hBdef
    have hRj : a j ≤ R := by linarith
    rw [abs_le] at hD
    obtain ⟨hD1, hD2⟩ := hD
    obtain ⟨wc, ws, hw, hclose⟩ := triangle_closes A B (a j) (by linarith) (by linarith)
      (ha j) (by rw [abs_le]; constructor <;> linarith) (by linarith)
    -- 残りの単位ベクトル
    let c0 : ι → ℝ := fun i => (1 + σ i) / 2 + (1 - σ i) / 2 * wc
    let s0 : ι → ℝ := fun i => (1 - σ i) / 2 * ws
    let c := Function.update c0 j (-(A + B * wc) / a j)
    let s := Function.update s0 j (-(B * ws) / a j)
    have hu : ∀ i, c i ^ 2 + s i ^ 2 = 1 := by
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [c, s, Function.update_self]
        rw [div_pow, div_pow, ← add_div, neg_sq, neg_sq, hclose]
        field_simp
      · simp only [c, s, Function.update_of_ne hi, c0, s0]
        rcases hσ i with h | h <;> rw [h] <;> nlinarith [hw]
    refine ⟨corrOf c s, corrOf_isCorr c s hu, ?_⟩
    rw [Q_corrOf]
    have hc : ∑ i, a i * c i = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hT : ∑ i ∈ T, a i * c i = A + B * wc := by
        rw [Finset.sum_congr rfl (fun i hi =>
          by rw [show c i = c0 i from Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _])]
        have e : ∀ i, a i * c0 i = (1 / 2) * a i + (1 / 2) * (σ i * a i) +
            wc * ((1 / 2) * a i - (1 / 2) * (σ i * a i)) := fun i => by simp only [c0]; ring
        simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [hAdef, hBdef, hR, hDdef]; ring
      rw [hT]
      simp only [c, Function.update_self]
      field_simp
      ring
    have hs : ∑ i, a i * s i = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hT : ∑ i ∈ T, a i * s i = B * ws := by
        rw [Finset.sum_congr rfl (fun i hi =>
          by rw [show s i = s0 i from Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _])]
        have e : ∀ i, a i * s0 i = ws * ((1 / 2) * a i - (1 / 2) * (σ i * a i)) :=
          fun i => by simp only [s0]; ring
        simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [hBdef, hR, hDdef]; ring
      rw [hT]
      simp only [s, Function.update_self]
      field_simp
      ring
    rw [hc, hs]; norm_num

/-- 最小値はちょうど (max(0, 2a_max − Σa))²。 -/
theorem Q_isLeast {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (j : ι) (hj : ∀ i, a i ≤ a j) :
    IsLeast {q | ∃ ρ, IsCorr ρ ∧ Q ρ a = q} ((max 0 (2 * a j - ∑ i, a i)) ^ 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ρ, hρ, hq⟩ := Q_attain ha j hj; exact ⟨ρ, hρ, hq⟩
  · rintro q ⟨ρ, hρ, rfl⟩; exact Q_lower hρ ha j

/-- (3) 一次の式を 0 にできる ⇔ 最大の寄与 ≤ 残りの寄与の和（多角形の不等式）。 -/
theorem Q_zero_iff {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (j : ι) (hj : ∀ i, a i ≤ a j) :
    (∃ ρ, IsCorr ρ ∧ Q ρ a = 0) ↔ a j ≤ ∑ i ∈ univ.erase j, a i := by
  have hsplit : ∑ i, a i = a j + ∑ i ∈ univ.erase j, a i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  constructor
  · rintro ⟨ρ, hρ, h0⟩
    have := Q_lower hρ ha j
    rw [h0] at this
    have hm : max 0 (2 * a j - ∑ i, a i) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (le_antisymm this (sq_nonneg _))
      exact this
    have := le_max_right 0 (2 * a j - ∑ i, a i)
    rw [hm] at this
    linarith
  · intro h
    obtain ⟨ρ, hρ, hq⟩ := Q_attain ha j hj
    refine ⟨ρ, hρ, ?_⟩
    rw [hq, max_eq_left (by linarith)]; norm_num

end Paper963

end Yamagishi
