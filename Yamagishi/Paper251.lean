/-
論文251『二次元で特別なのは一つではない』の芯「反転だけで調和性が保たれるのは d = 2 のときだけ」を、
すべての次元 d で機械に確かめさせる（格上げ）。

原稿（251_yamagishi_special_in_two_dimensions_is_not_one/…_jp.tex）が示している事：
  検算 4.1：u(x) = x₁（全次元で調和）を反転 x ↦ x/|x|² で因子なしに引き戻した関数と、r^(2−d) を掛けた
  関数（ケルビン変換）のラプラシアンを、d = 2〜6 で差分の数値で測り、因子なしで 0 になるのは d = 2 だけ
  （d = 3 で −1.728 など）。観察 4.3：因子は r^(2−d) で、d = 2 で r⁰ = 1。
  一般の証明は書いていない（射程で、複素解析を使わず差分で測っただけと明記）。

ここで証明した一般の言明（d = n + 1 ≥ 1 次元、x ≠ 0 の点で。|x|² = S）：
  (1) 一般の式：任意の実数 p について、x₁ |x|^(−2p) のラプラシアンは 2p(2p − d) x₁ |x|^(−2p−2)。
  (2) p = 1（反転で因子なしに引き戻した x₁/|x|²）：ラプラシアンは 2(2 − d) x₁/|x|⁴。
      だから x₁ ≠ 0 の点で調和 ⇔ d = 2。
  (3) p = d/2（ケルビン変換 |x|^(2−d) · x₁/|x|² = x₁|x|^(−d)）：ラプラシアンはどの d でも 0。
足した仮定・形式化の線：ラプラシアンは「座標の向きの二階微分の和」Σᵢ ∂ᵢ² とし、各 ∂ᵢ² は
直線 t ↦ f(x + t eᵢ) の二階微分として、一階の微分が 0 の近くで在ること（HasDerivAt）と、
その導関数の t = 0 での微分の値を示す形で書いた（Mathlib の `laplacian` とは結んでいない）。
空間は Fin (n+1) → ℝ に、|x|² = Σ xⱼ² を置いた。言明は原稿の一つの関数 u = x₁ についてで、
「すべての調和関数が反転で保たれる ⇔ d = 2」という一般の形（d = 2 の側は共形写像の性質）は示していない。
d ≠ 2 で保たれない側は、この一つの関数で十分（反例）。

形式化していないもの：平均値の性質と最大値原理の検算（第3節）、z² による引き戻し（観察 4.4）、
基本解の退化 (r^(2−d) − 1)/(2−d) → log r（検算 5.1）、ホイヘンスの原理との別根の判定、論文1 との関係。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper251

open Real Filter

/-- 直線に沿った二階微分の部品：φ(t) = (A + tc)(S + 2bt + t²)^(−p) の一階の導関数。 -/
noncomputable def φ1 (A c S b p : ℝ) (t : ℝ) : ℝ :=
  c * (S + 2 * b * t + t ^ 2) ^ (-p) +
    (A + t * c) * (-p * (S + 2 * b * t + t ^ 2) ^ (-p - 1)) * (2 * b + 2 * t)

/-- その t = 0 での微分（二階微分の値）。 -/
noncomputable def φ2 (A c S b p : ℝ) : ℝ :=
  2 * c * (-p * S ^ (-p - 1)) * (2 * b) +
    A * ((-p) * (-p - 1) * S ^ (-p - 2) * (2 * b) ^ 2 + (-p * S ^ (-p - 1)) * 2)

theorem line_derivs (A c S b p : ℝ) (hS : 0 < S) :
    (∀ᶠ t in nhds 0, HasDerivAt (fun t => (A + t * c) * (S + 2 * b * t + t ^ 2) ^ (-p))
      (φ1 A c S b p t) t) ∧ HasDerivAt (φ1 A c S b p) (φ2 A c S b p) 0 := by
  set q : ℝ → ℝ := fun t => S + 2 * b * t + t ^ 2
  have hq : ∀ t, HasDerivAt q (2 * b + 2 * t) t := by
    intro t
    have := (((hasDerivAt_id' t).const_mul (2 * b)).const_add S).add (hasDerivAt_pow 2 t)
    convert this using 1; push_cast; ring
  have hqc : Continuous q := by fun_prop
  have hpos : ∀ᶠ t in nhds 0, 0 < q t := by
    have : 0 < q 0 := by simp [q, hS]
    exact hqc.continuousAt.eventually (lt_mem_nhds this)
  have hlin : ∀ t, HasDerivAt (fun t => A + t * c) c t := by
    intro t; simpa using ((hasDerivAt_id' t).mul_const c).const_add A
  constructor
  · filter_upwards [hpos] with t ht
    have h1 := (hq t).rpow_const (p := -p) (Or.inl ht.ne')
    have := (hlin t).mul h1
    convert this using 1
    unfold φ1
    simp only [q]
    ring_nf
  · have h0 : 0 < q 0 := by simp [q, hS]
    have hA := (hq 0).rpow_const (p := -p) (Or.inl h0.ne')
    have hB := (hq 0).rpow_const (p := -p - 1) (Or.inl h0.ne')
    have hL : HasDerivAt (fun t : ℝ => 2 * b + 2 * t) 2 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul 2).const_add (2 * b)
    have h := ((hA.const_mul c).add ((((hlin 0).mul (hB.const_mul (-p))).mul hL)))
    have e : φ1 A c S b p =
        fun t => c * q t ^ (-p) + (A + t * c) * (-p * q t ^ (-p - 1)) * (2 * b + 2 * t) := by
      ext t; simp [φ1, q]
    rw [e]
    convert h using 1
    unfold φ2
    simp only [q]
    norm_num
    rw [show -p - 1 - 1 = -p - 2 by ring]
    ring

/-- 座標の向きの単位ベクトル eᵢ。 -/
def e {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → ℝ := Pi.single i 1

theorem e_apply {n : ℕ} (i j : Fin (n + 1)) : e i j = if j = i then 1 else 0 := by
  simp [e, Pi.single_apply]

/-- 座標の向き eᵢ に沿った |x + t eᵢ|² = S + 2t xᵢ + t²。 -/
theorem norm_sq_line {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (t : ℝ) :
    ∑ j, (x j + t * e i j) ^ 2 = (∑ j, x j ^ 2) + 2 * x i * t + t ^ 2 := by
  have : ∀ j, (x j + t * e i j) ^ 2 =
      x j ^ 2 + 2 * t * (x j * e i j) + t ^ 2 * e i j := by
    intro j
    by_cases h : j = i
    · subst h; simp [e_apply]; ring
    · simp [e_apply, h]
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [e_apply]
  ring

/-- f_p(y) = y₁ · (Σ yⱼ²)^(−p) = y₁ |y|^(−2p)。 -/
noncomputable def fp {n : ℕ} (p : ℝ) (y : Fin (n + 1) → ℝ) : ℝ := y 0 * (∑ j, y j ^ 2) ^ (-p)

/-- (1) 各 ∂ᵢ² fp(x)：直線 t ↦ fp(x + t eᵢ) の一階の導関数が 0 の近くで在り、その t = 0 での微分が
φ2(x₁, δᵢ₁, S, xᵢ, p)。 -/
theorem second_partial {n : ℕ} (p : ℝ) (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2)
    (i : Fin (n + 1)) :
    (∀ᶠ t in nhds 0, HasDerivAt (fun t => fp p (x + t • e i))
      (φ1 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) p t) t) ∧
    HasDerivAt (φ1 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) p)
      (φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) p) 0 := by
  obtain ⟨h1, h2⟩ := line_derivs (x 0) (e i 0) (∑ j, x j ^ 2) (x i) p hx
  refine ⟨?_, h2⟩
  filter_upwards [h1] with t ht
  have hfun : (fun t => fp p (x + t • e i)) =
      fun t => (x 0 + t * e i 0) *
        ((∑ j, x j ^ 2) + 2 * x i * t + t ^ 2) ^ (-p) := by
    ext s
    simp only [fp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [norm_sq_line x i s]
  rw [hfun]
  convert ht using 2

/-- (1) 一般の式：Σᵢ ∂ᵢ² (x₁|x|^(−2p)) = 2p(2p − d) x₁ |x|^(−2p−2)、d = n + 1。 -/
theorem laplacian_fp {n : ℕ} (p : ℝ) (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2) :
    ∑ i, φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) p =
      2 * p * (2 * p - (n + 1)) * x 0 * (∑ j, x j ^ 2) ^ (-p - 1) := by
  set S := ∑ j, x j ^ 2 with hSdef
  have e2 : S ^ (-p - 2) * S = S ^ (-p - 1) := by
    rw [show -p - 2 = (-p - 1) - 1 by ring, rpow_sub hx, rpow_one, div_mul_cancel₀ _ hx.ne']
  unfold φ2
  simp only [Finset.sum_add_distrib, mul_add]
  have hδ : ∀ i : Fin (n + 1), e i 0 = if i = 0 then 1 else 0 := by
    intro i; rw [e_apply]; by_cases h : i = 0
    · subst h; simp
    · simp [Ne.symm h, h]
  simp only [hδ]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs : ∑ i : Fin (n + 1), x 0 * ((-p) * (-p - 1) * S ^ (-p - 2) * (2 * x i) ^ 2) =
      4 * p * (p + 1) * x 0 * (S ^ (-p - 2) * S) := by
    rw [hSdef, Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, e2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- (2) 反転で因子なしに引き戻した x₁/|x|²（p = 1）：ラプラシアンは 2(2 − d) x₁/|x|⁴。 -/
theorem inversion_laplacian {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2) :
    (∀ y : Fin (n + 1) → ℝ, fp 1 y = y 0 / ∑ j, y j ^ 2) ∧
    ∑ i, φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) 1 =
      2 * (2 - (n + 1)) * x 0 / (∑ j, x j ^ 2) ^ 2 := by
  constructor
  · intro y; simp [fp, rpow_neg_one, div_eq_mul_inv]
  · rw [laplacian_fp 1 x hx, show (-(1 : ℝ) - 1) = -2 by ring, rpow_neg hx.le]
    norm_num
    field_simp

/-- (2) 反転で因子なしに引き戻した x₁/|x|² が、x₁ ≠ 0 の点で調和（ラプラシアン 0）⇔ d = n + 1 = 2。 -/
theorem inversion_harmonic_iff {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2)
    (hx0 : x 0 ≠ 0) :
    ∑ i, φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) 1 = 0 ↔ n + 1 = 2 := by
  rw [(inversion_laplacian x hx).2]
  have hS : (∑ j, x j ^ 2) ^ 2 ≠ 0 := by positivity
  rw [div_eq_zero_iff, or_iff_left hS, mul_eq_zero, or_iff_left hx0, mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · have : (n : ℝ) = 1 := by linarith
      have : n = 1 := by exact_mod_cast this
      omega
  · intro h
    right
    have : (n : ℝ) = 1 := by exact_mod_cast (by omega : n = 1)
    linarith

/-- (3) ケルビン変換（|x|^(2−d) を掛けた x₁|x|^(−d)、p = d/2）：ラプラシアンはどの次元でも 0。 -/
theorem kelvin_harmonic {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2) :
    ∑ i, φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) (((n : ℝ) + 1) / 2) = 0 := by
  rw [laplacian_fp _ x hx]
  ring

/-- (1) の特別な場合 p = 0：u = x₁ そのものは調和（どの次元でも）。 -/
theorem coordinate_harmonic {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : 0 < ∑ j, x j ^ 2) :
    ∑ i, φ2 (x 0) (e i 0) (∑ j, x j ^ 2) (x i) 0 = 0 := by
  rw [laplacian_fp _ x hx]
  ring

end Paper251

end Yamagishi
