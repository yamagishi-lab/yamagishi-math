/-
論文284『ラングミュア吸着とフェルミ分布は、同じ一つの式である』の格上げ（一般の形・多項式の場合）。

原稿（284_yamagishi_the_same_exclusion_gives_the_same_distribution/…_jp.tex）は、
変数の置き換え Kp = e^((μ−E)/kT) で二つの式が同じになることを示し、根として一つの席の大分配関数
Ξ = 1 + e^((μ−E)/kT) が二項で止まること（席が 0 か 1 ならこの形、という前向き）を挙げている。
圧力の倍率 11・10.0909・999 倍はオッズ比の数値例。

ここで証明した言明（一つの席の大分配関数 Ξ(z) = Σ g_n z^n を実係数の多項式とし、K > 0）：
  (1) `occupancy_forward`：Ξ = g₀(1 + Kz)（g₀ ≠ 0）なら、すべての z > 0 で平均占有数
      ⟨n⟩ = zΞ′(z)/Ξ(z) は Kz/(1 + Kz)（ラングミュア＝フェルミの形）。
  (2) `occupancy_converse`：ある区間 (0, ε) のすべての z で Ξ(z) ≠ 0 かつ ⟨n⟩ = Kz/(1 + Kz) なら、
      Ξ = g₀(1 + Kz)、すなわち g₁ = Kg₀、n ≥ 2 で g_n = 0（一つの席は 0 か 1 しか取らない）。
      `coeff_relation`：その芯は係数の関係 (n + 1)g_{n+1} = K(1 − n)g_n。
  (3) `odds_ratio_eq`・`odds_ratio_gt_ten`・`odds_ratio_strictMono`・`odds_ratio_tendsto`：被覆率を
      1 − ε から 1 − ε/10 に上げるのに要る圧力の倍率は (10 − ε)/(1 − ε) で、いつも 10 より大きく、
      ε について狭義に増え、ε → 0 で 10 に近づく（ε = 0.1 で 11、0.01 で 10.0909…）。
足した仮定：Ξ を多項式に限った（席の最大占有数が有限）。係数の符号（g_n ≥ 0）は (2) に要らない。
形式化していないもの：Ξ が無限の冪級数の場合（一致の定理で係数を比べる所）、ミカエリス＝メンテンの式
（定常状態近似という別の道で同じ形になるので、この逆向きは当てはまらない）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For a one-site grand partition function that is a polynomial, the mean occupancy zΞ′/Ξ equals the
Langmuir–Fermi form Kz/(1 + Kz) on an interval exactly when Ξ = g₀(1 + Kz), that is, when the site
holds zero or one particle; the pressure factor per decade of vacancy is (10 − ε)/(1 − ε) → 10.
-/
import Mathlib

namespace Yamagishi

namespace Paper284

open Polynomial Set Filter Topology

/-- (1) 前向き：Ξ = g₀(1 + Kz) なら ⟨n⟩ = Kz/(1 + Kz)。 -/
theorem occupancy_forward {g0 K z : ℝ} (hg : g0 ≠ 0) (hK : 0 < K) (hz : 0 < z) :
    let Ξ : ℝ[X] := C g0 * (1 + C K * X)
    z * (derivative Ξ).eval z / Ξ.eval z = K * z / (1 + K * z) := by
  intro Ξ
  have h1 : 0 < 1 + K * z := by positivity
  simp only [Ξ, derivative_mul, derivative_C, zero_mul, zero_add, derivative_add, derivative_one,
    derivative_X, mul_one, eval_mul, eval_C, eval_add, eval_one, eval_X]
  field_simp

/-- 多項式 P = X·Ξ′·(1 + KX) − K·X·Ξ の係数：coeff P (n + 1) = (n + 1)g_{n+1} + K(n − 1)g_n。 -/
theorem coeff_P (Ξ : ℝ[X]) (K : ℝ) (n : ℕ) :
    (X * derivative Ξ * (1 + C K * X) - C K * X * Ξ).coeff (n + 1) =
      ((n : ℝ) + 1) * Ξ.coeff (n + 1) + K * ((n : ℝ) - 1) * Ξ.coeff n := by
  have e : X * derivative Ξ * (1 + C K * X) - C K * X * Ξ =
      X * derivative Ξ + C K * (X * (X * derivative Ξ)) - C K * (X * Ξ) := by ring
  rw [e, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_X_mul, coeff_X_mul,
    coeff_derivative]
  rcases n with _ | m
  · simp; ring
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- (2) の芯：区間で ⟨n⟩ = Kz/(1 + Kz) なら、P = 0 で、係数の関係 (n + 1)g_{n+1} = K(1 − n)g_n。 -/
theorem coeff_relation {Ξ : ℝ[X]} {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hne : ∀ z ∈ Ioo 0 ε, Ξ.eval z ≠ 0)
    (hocc : ∀ z ∈ Ioo 0 ε, z * (derivative Ξ).eval z / Ξ.eval z = K * z / (1 + K * z))
    (n : ℕ) : ((n : ℝ) + 1) * Ξ.coeff (n + 1) = K * (1 - (n : ℝ)) * Ξ.coeff n := by
  set P : ℝ[X] := X * derivative Ξ * (1 + C K * X) - C K * X * Ξ with hP
  have hroot : ∀ z ∈ Ioo 0 ε, P.IsRoot z := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have h1 : 0 < 1 + K * z := by positivity
    have h := hocc z hz
    rw [div_eq_div_iff (hne z hz) h1.ne'] at h
    simp only [IsRoot, hP, eval_sub, eval_mul, eval_X, eval_add, eval_one, eval_C]
    linarith
  have hP0 : P = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (fun z hz => hroot z hz)
    exact Ioo_infinite hε
  have := coeff_P Ξ K n
  rw [← hP, hP0, coeff_zero] at this
  linarith

/-- (2) 逆向き：区間 (0, ε) で ⟨n⟩ = Kz/(1 + Kz) なら Ξ = g₀(1 + Kz)。 -/
theorem occupancy_converse {Ξ : ℝ[X]} {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hne : ∀ z ∈ Ioo 0 ε, Ξ.eval z ≠ 0)
    (hocc : ∀ z ∈ Ioo 0 ε, z * (derivative Ξ).eval z / Ξ.eval z = K * z / (1 + K * z)) :
    Ξ = C (Ξ.coeff 0) * (1 + C K * X) := by
  have rel := coeff_relation hK hε hne hocc
  have h1 : Ξ.coeff 1 = K * Ξ.coeff 0 := by have := rel 0; simp at this; linarith
  have h2 : ∀ m : ℕ, Ξ.coeff (m + 2) = 0 := by
    intro m
    induction m with
    | zero => have := rel 1; norm_num at this; linarith
    | succ k ih =>
      have := rel (k + 2)
      rw [ih, mul_zero] at this
      have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) + 1 := by positivity
      have := (mul_eq_zero.mp this).resolve_left hpos.ne'
      simpa [add_assoc] using this
  ext n
  rcases n with _ | _ | m
  · simp
  · simp [h1, coeff_one]; ring
  · rw [h2 m]
    simp [coeff_one]

/-- (3) 被覆率を 1 − ε から 1 − ε/10 に上げる圧力の倍率（オッズの比）。 -/
noncomputable def oddsRatio (ε : ℝ) : ℝ := ((1 - ε / 10) / (ε / 10)) / ((1 - ε) / ε)

theorem odds_ratio_eq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : oddsRatio ε = (10 - ε) / (1 - ε) := by
  have : 0 < 1 - ε := by linarith
  unfold oddsRatio
  field_simp

theorem odds_ratio_gt_ten {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 10 < oddsRatio ε := by
  rw [odds_ratio_eq h0 h1, lt_div_iff₀ (by linarith)]
  linarith

theorem odds_ratio_strictMono : StrictMonoOn oddsRatio (Ioo 0 1) := by
  intro a ha b hb hab
  rw [odds_ratio_eq ha.1 ha.2, odds_ratio_eq hb.1 hb.2,
    div_lt_div_iff₀ (by linarith [ha.2]) (by linarith [hb.2])]
  nlinarith

theorem odds_ratio_tendsto : Tendsto oddsRatio (𝓝[>] 0) (𝓝 10) := by
  have hev : (fun ε => (10 - ε) / (1 - ε)) =ᶠ[𝓝[>] 0] oddsRatio := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (odds_ratio_eq hε.1 hε.2).symm
  apply Tendsto.congr' hev
  have : Tendsto (fun ε : ℝ => (10 - ε) / (1 - ε)) (𝓝 0) (𝓝 ((10 - 0) / (1 - 0))) := by
    exact Tendsto.div (tendsto_const_nhds.sub tendsto_id) (tendsto_const_nhds.sub tendsto_id)
      (by rw [sub_zero]; exact one_ne_zero)
  rw [show ((10 : ℝ) - 0) / (1 - 0) = 10 by norm_num] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- 原稿の表の二つの値：ε = 0.1 で 11、ε = 0.01 で 1110/110 = 10.0909…。 -/
theorem paper_values : oddsRatio 0.1 = 11 ∧ oddsRatio 0.01 = 111 / 11 := by
  unfold oddsRatio; constructor <;> norm_num

end Paper284

end Yamagishi
