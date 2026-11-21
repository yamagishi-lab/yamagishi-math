/-
論文235『「境界条件」は四つあり、方程式を一文字も変えずに固有値が全部動く』の格上げ（一般の形）。

原稿（235_yamagishi_four_boundary_conditions/…_jp.tex）は、区間 [0, 1] の −u″ = λu に
u′(0) = h u(0)、u′(1) = −h u(1)（ロバン条件）を課し、h = 0, −0.5, −1, −2, −5, −10 の有限要素の数値で
最小固有値を測っている。変分形の境界項が負に効くことは言葉で述べるが、符号を一般に示してはいない。

ここで証明した言明（u は二回微分でき、u″ は連続）：
  (1) `green`：固有関数なら λ∫₀¹u² = ∫₀¹u′² + h(u(0)² + u(1)²)（グリーンの式・レイリー商の形）。
  (2) `eigen_nonneg`：h ≥ 0 なら、どの固有値も λ ≥ 0（固有関数は ∫u² > 0 とする）。
      `eigen_zero`：h = 0 では λ = 0 が固有値（u ≡ 1）。
  (3) `neg_eigen_exists`：h < 0 なら、μ tanh(μ/2) = −h を満たす μ > 0 があり、
      u(x) = cosh(μ(x − 1/2)) は固有値 λ = −μ² の固有関数で、λ ≤ 2h < 0。
      したがって最小固有値は 2h 以下で、負（下読みの AI の筋はレイリー商に u ≡ 1 を入れる形だが、
      ここでは固有関数を作って示した。最小固有値がレイリー商の下限であることは使っていない）。
  部品 `tanh_le_self`：x ≥ 0 で tanh x ≤ x。
足した仮定：(2) の固有関数は ∫u² > 0（零でない）とした。形式化していないもの：h > 0 で λ > 0 の
狭義の不等式、最小固有値の存在（スペクトルの理論）、h → −∞ で λ₁ ≈ −h²、正方形の表。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper235

open Real Set intervalIntegral

/-- 固有関数の条件：u′、u″ を持ち、−u″ = λu、ロバン条件。 -/
structure IsEigen (h lam : ℝ) (u u' u'' : ℝ → ℝ) : Prop where
  du : ∀ x, HasDerivAt u (u' x) x
  du' : ∀ x, HasDerivAt u' (u'' x) x
  cont : Continuous u''
  eq : ∀ x, -u'' x = lam * u x
  bc0 : u' 0 = h * u 0
  bc1 : u' 1 = -h * u 1

/-- (1) グリーンの式。 -/
theorem green {h lam : ℝ} {u u' u'' : ℝ → ℝ} (e : IsEigen h lam u u' u'') :
    lam * ∫ x in (0 : ℝ)..1, u x ^ 2 =
      (∫ x in (0 : ℝ)..1, u' x ^ 2) + h * (u 0 ^ 2 + u 1 ^ 2) := by
  have hu'c : Continuous u' := continuous_iff_continuousAt.2 fun x => (e.du' x).continuousAt
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (e.du x).continuousAt
  have hibp := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (fun x _ => e.du x)
    (fun x _ => e.du' x) (hu'c.intervalIntegrable _ _) (e.cont.intervalIntegrable _ _)
  have h1 : ∫ x in (0 : ℝ)..1, u x * u'' x = -(lam * ∫ x in (0 : ℝ)..1, u x ^ 2) := by
    rw [← integral_const_mul, ← integral_neg]
    apply integral_congr
    intro x _
    have := e.eq x
    show u x * u'' x = -(lam * u x ^ 2)
    rw [show u'' x = -(lam * u x) by linarith]; ring
  have h2 : ∫ x in (0 : ℝ)..1, u' x * u' x = ∫ x in (0 : ℝ)..1, u' x ^ 2 := by
    apply integral_congr; intro x _; simp only; ring
  rw [h1, h2, e.bc0, e.bc1] at hibp
  linarith

/-- (2) h ≥ 0 なら固有値は 0 以上。 -/
theorem eigen_nonneg {h lam : ℝ} {u u' u'' : ℝ → ℝ} (e : IsEigen h lam u u' u'') (hh : 0 ≤ h)
    (hu : 0 < ∫ x in (0 : ℝ)..1, u x ^ 2) : 0 ≤ lam := by
  have hg := green e
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, u' x ^ 2 :=
    integral_nonneg zero_le_one (fun x _ => sq_nonneg _)
  have : 0 ≤ lam * ∫ x in (0 : ℝ)..1, u x ^ 2 := by
    rw [hg]; have := mul_nonneg hh (add_nonneg (sq_nonneg (u 0)) (sq_nonneg (u 1))); linarith
  exact nonneg_of_mul_nonneg_left this hu

/-- (2) h = 0 では 0 が固有値。 -/
theorem eigen_zero : IsEigen 0 0 (fun _ => 1) (fun _ => 0) (fun _ => 0) where
  du := fun x => hasDerivAt_const x 1
  du' := fun x => hasDerivAt_const x 0
  cont := continuous_const
  eq := fun x => by simp
  bc0 := by simp
  bc1 := by simp

/-- 部品：x ≥ 0 で tanh x ≤ x。 -/
theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : tanh x ≤ x := by
  have hmono : MonotoneOn (fun x => x * cosh x - sinh x) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous fun x => x * cosh x - sinh x).continuousOn
    · exact (by fun_prop : Differentiable ℝ fun x => x * cosh x - sinh x).differentiableOn
    · intro y hy
      rw [interior_Ici] at hy
      have hd : HasDerivAt (fun x => x * cosh x - sinh x) (y * sinh y) y := by
        have := ((hasDerivAt_id' y).mul (hasDerivAt_cosh y)).sub (hasDerivAt_sinh y)
        exact this.congr_deriv (by ring)
      rw [hd.deriv]
      exact mul_nonneg (le_of_lt hy) (sinh_nonneg_iff.2 (le_of_lt hy))
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simp at this
  rw [tanh_eq_sinh_div_cosh, div_le_iff₀ (cosh_pos x)]
  linarith

/-- μ tanh(μ/2) の連続性。 -/
theorem continuous_phi : Continuous fun μ : ℝ => μ * tanh (μ / 2) := by
  have : Continuous fun μ : ℝ => μ * (sinh (μ / 2) / cosh (μ / 2)) :=
    continuous_id.mul ((by fun_prop : Continuous fun μ : ℝ => sinh (μ / 2)).div
      (by fun_prop) (fun μ => (cosh_pos _).ne'))
  simpa [tanh_eq_sinh_div_cosh] using this

/-- (3) h < 0 なら、固有値 −μ² ≤ 2h の固有関数 cosh(μ(x − 1/2)) がある。 -/
theorem neg_eigen_exists {h : ℝ} (hh : h < 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ * tanh (μ / 2) = -h ∧
      IsEigen h (-μ ^ 2) (fun x => cosh (μ * (x - 1 / 2))) (fun x => μ * sinh (μ * (x - 1 / 2)))
        (fun x => μ ^ 2 * cosh (μ * (x - 1 / 2))) ∧ -μ ^ 2 ≤ 2 * h := by
  -- μ を中間値の定理で選ぶ（M ≥ 2 なら tanh(M/2) ≥ 1/2）
  set M := max 2 (-2 * h) with hM
  have hM2 : 2 ≤ M := le_max_left _ _
  have htM : 1 / 2 ≤ tanh (M / 2) := by
    rw [tanh_eq_sinh_div_cosh, le_div_iff₀ (cosh_pos _), sinh_eq, cosh_eq]
    have he : exp (M / 2) * exp (-(M / 2)) = 1 := by rw [← exp_add]; simp
    have h3 : 3 ≤ exp (M / 2) * exp (M / 2) := by
      rw [← exp_add, show M / 2 + M / 2 = M by ring]
      have := add_one_le_exp M; linarith
    have hp : 0 < exp (-(M / 2)) := exp_pos _
    nlinarith
  have hφM : -h ≤ M * tanh (M / 2) := by
    have : -2 * h ≤ M := le_max_right _ _
    nlinarith
  obtain ⟨μ, ⟨hμ0, hμM⟩, hμ⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ M)
    continuous_phi.continuousOn ⟨by simp; linarith, hφM⟩
  have hμpos : 0 < μ := by
    rcases eq_or_lt_of_le hμ0 with h0 | h0
    · rw [← h0] at hμ; simp at hμ; linarith
    · exact h0
  refine ⟨μ, hμpos, hμ, ?_, ?_⟩
  · have hc : cosh (μ / 2) ≠ 0 := (cosh_pos _).ne'
    have htanh : tanh (μ / 2) * cosh (μ / 2) = sinh (μ / 2) := by
      rw [tanh_eq_sinh_div_cosh]; field_simp
    have hhμ : h = -(μ * tanh (μ / 2)) := by linarith
    have hlin : ∀ x : ℝ, HasDerivAt (fun x => μ * (x - 1 / 2)) μ x := by
      intro x
      have := ((hasDerivAt_id x).sub_const (1 / 2)).const_mul μ
      simpa using this
    refine ⟨?_, ?_, by fun_prop, ?_, ?_, ?_⟩
    · intro x
      exact ((hasDerivAt_cosh _).comp x (hlin x)).congr_deriv (mul_comm _ _)
    · intro x
      exact (((hasDerivAt_sinh _).comp x (hlin x)).const_mul μ).congr_deriv (by ring)
    · intro x; ring
    · show μ * sinh (μ * (0 - 1 / 2)) = h * cosh (μ * (0 - 1 / 2))
      rw [show μ * (0 - 1 / 2) = -(μ / 2) by ring, sinh_neg, cosh_neg, hhμ, neg_mul, mul_assoc,
        htanh]
      ring
    · show μ * sinh (μ * (1 - 1 / 2)) = -h * cosh (μ * (1 - 1 / 2))
      rw [show μ * (1 - 1 / 2) = μ / 2 by ring, hhμ, neg_neg, mul_assoc, htanh]
  · have := tanh_le_self (by linarith : (0 : ℝ) ≤ μ / 2)
    nlinarith

end Paper235

end Yamagishi
