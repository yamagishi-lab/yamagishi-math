/-
論文960『最も安い箱の数は、取り除く桁数に比例する』の格上げ（一般の形）。

原稿（960_yamagishi_the_cheapest_number_of_tanks_in_series_scales_with_decades_to_remove/…_jp.tex）は、
同じ大きさの完全混合槽 N 個の直列で一次反応の残りを r = (1+x)^(−N) にし、箱一つの費用を x^a と
置いて、合計の費用 C = N x^a = ln(1/r)·x^a/ln(1+x) を考え、微分を 0 と置いた a(1+x)ln(1+x) = x の解
を a = 0.4〜0.95 の五つで数値で求め、整数の箱の数の最安を残り 0.1・0.01・0.001 の三通りで探して
「ちょうど 1:2:3」と数えている。a = 1 では最安が無い（費用は押し出し流れの ln(1/r) に近づく）とする。

ここで証明した言明（x > 0 は箱一つの kτ、K(x) = x^a/ln(1+x)、C = ln(1/r)·K）：
  (1) `h_strictMonoOn`：h(x) = (1+x)ln(1+x)/x は (0, ∞) で狭義に増え、`one_lt_h`：h > 1。
  (2) `exists_unique_xstar`：0 < a < 1 なら a·h(x) = 1（すなわち a(1+x)ln(1+x) = x）の解 x* > 0 は
      ただ一つ。`K_min`：K は x* でただ一つの最小をとる（r によらない）。
  (3) `K_strictMonoOn_of_one_le`：a ≥ 1 なら K は (0, ∞) で狭義に増え、最小は無い。
      `K_le_of_eq_one`：a = 1 なら 1 < K(x) ≤ 1 + x（下限 1 は押し出し流れ、届かない）。
      `K_le_of_one_lt`：a > 1 なら K(x) ≤ x^(a−1)(1+x) で、箱を増やす（x → 0）ほど 0 に近づく。
  (4) 整数の箱の数での比例は一般には崩れる（下読みの AI の指摘を数で確かめた）：
      `cost61_lt_cost60`：a = 0.6・残り 10^(−30) で、61 個の費用 < 60 個の費用
      （60 個は、残り 0.1 で最安の 2 個を 30 倍した数）。費用は N·(10^(30/N) − 1)^0.6。
定義に置いたもの：完全混合槽の直列の残り (1+x)^(−N)（原稿の式）と、費用 x^a（原稿の置き方）。
差：原稿の「ちょうど 1:2:3」は桁数の小さい三つでたまたま丸めがそろったもので、比例が成り立つのは
連続に広げた箱の数 ln(1/r)/ln(1+x*) の方に限る。61 個が全体の最安であることまでは示していない
（示したのは 60 個が最安でないこと）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper960

open Real Set

/-- h(x) = (1+x)ln(1+x)/x。 -/
noncomputable def h (x : ℝ) : ℝ := (1 + x) * log (1 + x) / x

/-- 費用の ln(1/r) 以外の部分 K(x) = x^a/ln(1+x)。 -/
noncomputable def K (a x : ℝ) : ℝ := x ^ a / log (1 + x)

theorem log_lt_self {x : ℝ} (hx : 0 < x) : log (1 + x) < x := by
  have := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1 + x) (by linarith : 1 + x ≠ 1)
  linarith

theorem log_pos' {x : ℝ} (hx : 0 < x) : 0 < log (1 + x) := Real.log_pos (by linarith)

theorem hasDerivAt_h {x : ℝ} (hx : 0 < x) :
    HasDerivAt h ((x - log (1 + x)) / x ^ 2) x := by
  have h1 : HasDerivAt (fun y => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have h2 : HasDerivAt (fun y => log (1 + y)) (1 / (1 + x)) x := by
    have := h1.log (by linarith)
    simpa using this
  have h3 := (h1.mul h2).div (hasDerivAt_id x) hx.ne'
  have e : h = ((fun y => 1 + y) * fun y => log (1 + y)) / id := by
    funext y; simp [h]
  rw [e]
  convert h3 using 1
  have : 0 < 1 + x := by linarith
  simp only [id, Pi.mul_apply]
  field_simp
  ring

/-- (1) h は (0, ∞) で狭義に増える。 -/
theorem h_strictMonoOn : StrictMonoOn h (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx; exact (hasDerivAt_h hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_h hx).deriv]
    have := log_lt_self hx
    have : 0 < x ^ 2 := by have := hx.out; positivity
    apply div_pos _ this
    linarith

/-- ln(1+x) > x/(1+x)。 -/
theorem div_lt_log {x : ℝ} (hx : 0 < x) : x / (1 + x) < log (1 + x) := by
  have h1 : 0 < 1 + x := by linarith
  have hne : (1 + x)⁻¹ ≠ 1 := by
    intro h; have : 1 + x = 1 := by simpa using congrArg (·⁻¹) h
    linarith
  have := Real.log_lt_sub_one_of_pos (inv_pos.mpr h1) hne
  rw [Real.log_inv] at this
  have e : x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
  linarith

/-- h > 1（すなわち (1+x)ln(1+x) > x）。 -/
theorem one_lt_h {x : ℝ} (hx : 0 < x) : 1 < h x := by
  unfold h
  rw [one_lt_div hx]
  have h1 : 0 < 1 + x := by linarith
  have := div_lt_log hx
  rw [div_lt_iff₀ h1] at this
  linarith

/-- h < 1 + x。 -/
theorem h_lt {x : ℝ} (hx : 0 < x) : h x < 1 + x := by
  unfold h
  rw [div_lt_iff₀ hx]
  have := log_lt_self hx
  have h1 : 0 < 1 + x := by linarith
  nlinarith

/-- K の微分：K′(x) = x^a/((1+x)ln²(1+x))·(a·h(x) − 1)。 -/
theorem hasDerivAt_K (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (K a) (x ^ a / ((1 + x) * log (1 + x) ^ 2) * (a * h x - 1)) x := by
  have hL := log_pos' hx
  have h1 : HasDerivAt (fun y => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have h2 : HasDerivAt (fun y => log (1 + y)) (1 / (1 + x)) x := by
    simpa using h1.log (by linarith)
  have h3 := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).div h2 hL.ne'
  unfold K
  convert h3 using 1
  unfold h
  rw [Real.rpow_sub_one hx.ne']
  have : 0 < 1 + x := by linarith
  field_simp

theorem K_factor_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < x ^ a / ((1 + x) * log (1 + x) ^ 2) := by
  have := log_pos' hx
  have : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  have : 0 < 1 + x := by linarith
  positivity

theorem h_continuousOn : ContinuousOn h (Ioi 0) := fun _ hx =>
  (hasDerivAt_h hx).continuousAt.continuousWithinAt

/-- (2) 0 < a < 1 なら a·h(x) = 1 の解 x* > 0 はただ一つ。 -/
theorem exists_unique_xstar {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃! x, 0 < x ∧ a * h x = 1 := by
  set x0 := (1 / a - 1) / 2 with hx0
  have h1a : 1 < 1 / a := by rw [lt_div_iff₀ ha0]; linarith
  have hx0p : 0 < x0 := by rw [hx0]; linarith
  set x1 := Real.exp (1 / a) with hx1
  have hx1p : 0 < x1 := Real.exp_pos _
  have hx01 : x0 < x1 := by
    have := Real.add_one_le_exp (1 / a)
    rw [hx0]; linarith
  have hlo : a * h x0 < 1 := by
    have := h_lt hx0p
    have : a * h x0 < a * (1 + x0) := mul_lt_mul_of_pos_left this ha0
    have e : a * (1 + x0) = a / 2 + 1 / 2 := by rw [hx0]; field_simp; ring
    linarith
  have hhi : 1 < a * h x1 := by
    have hL := log_pos' hx1p
    have e1 : log (1 + x1) < h x1 := by
      unfold h
      rw [lt_div_iff₀ hx1p]
      nlinarith
    have e2 : 1 / a < log (1 + x1) := by
      have : log x1 < log (1 + x1) := Real.log_lt_log hx1p (by linarith)
      rwa [hx1, Real.log_exp] at this
    have : 1 / a < h x1 := by linarith
    rw [div_lt_iff₀ ha0] at this
    linarith
  have hcont : ContinuousOn (fun x => a * h x) (Icc x0 x1) :=
    continuousOn_const.mul (h_continuousOn.mono
      (fun x (hx : x ∈ Icc x0 x1) => (lt_of_lt_of_le hx0p hx.1 : 0 < x)))
  obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc hx01.le hcont ⟨hlo.le, hhi.le⟩
  have hxp : 0 < x := lt_of_lt_of_le hx0p hx.1
  refine ⟨x, ⟨hxp, hxe⟩, ?_⟩
  rintro y ⟨hyp, hye⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h_strictMonoOn hyp hxp hlt
    have := mul_lt_mul_of_pos_left this ha0
    linarith
  · have := h_strictMonoOn hxp hyp hlt
    have := mul_lt_mul_of_pos_left this ha0
    linarith

theorem K_continuousOn (a : ℝ) : ContinuousOn (K a) (Ioi 0) := fun _ hx =>
  (hasDerivAt_K a hx).continuousAt.continuousWithinAt

/-- (2) a·h(x*) = 1 なら、K は x* でただ一つの最小をとる。 -/
theorem K_min {a xs : ℝ} (ha0 : 0 < a) (hxs : 0 < xs) (hst : a * h xs = 1) :
    ∀ y, 0 < y → y ≠ xs → K a xs < K a y := by
  intro y hy hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : StrictAntiOn (K a) (Icc y xs) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc y xs)
        ((K_continuousOn a).mono (fun z hz => lt_of_lt_of_le hy hz.1))
      intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hy hz.1
      rw [(hasDerivAt_K a hz0).deriv]
      have := h_strictMonoOn hz0 hxs hz.2
      have : a * h z - 1 < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg (K_factor_pos a hz0) this
    exact this ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  · have : StrictMonoOn (K a) (Icc xs y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc xs y)
        ((K_continuousOn a).mono (fun z hz => lt_of_lt_of_le hxs hz.1))
      intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hxs hz.1
      rw [(hasDerivAt_K a hz0).deriv]
      have := h_strictMonoOn hxs hz0 hz.1
      have : 0 < a * h z - 1 := by nlinarith
      exact mul_pos (K_factor_pos a hz0) this
    exact this ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt

/-- 合計の費用 ln(1/r)·K の最小の点は r によらない（0 < r < 1）。 -/
theorem cost_min_indep {a xs r : ℝ} (ha0 : 0 < a) (hxs : 0 < xs) (hst : a * h xs = 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ y, 0 < y → y ≠ xs → log (1 / r) * K a xs < log (1 / r) * K a y := by
  intro y hy hne
  have : 0 < log (1 / r) := Real.log_pos (by rw [lt_div_iff₀ hr0]; linarith)
  exact mul_lt_mul_of_pos_left (K_min ha0 hxs hst y hy hne) this

/-- (3) a ≥ 1 なら K は (0, ∞) で狭義に増え、最小は無い。 -/
theorem K_strictMonoOn_of_one_le {a : ℝ} (ha : 1 ≤ a) : StrictMonoOn (K a) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (K_continuousOn a)
  intro z hz
  rw [interior_Ioi] at hz
  rw [(hasDerivAt_K a hz).deriv]
  have h1 := one_lt_h hz
  have : 0 < a * h z - 1 := by nlinarith
  exact mul_pos (K_factor_pos a hz) this

theorem no_min_of_one_le {a : ℝ} (ha : 1 ≤ a) : ∀ x, 0 < x → ∃ y, 0 < y ∧ K a y < K a x :=
  fun x hx => ⟨x / 2, by positivity,
    K_strictMonoOn_of_one_le ha (show (0 : ℝ) < x / 2 by positivity) hx (half_lt_self hx)⟩

/-- a = 1：1 < K(x) ≤ 1 + x（下限 1 は押し出し流れで、届かない）。 -/
theorem K_le_of_eq_one {x : ℝ} (hx : 0 < x) : 1 < K 1 x ∧ K 1 x ≤ 1 + x := by
  unfold K
  rw [Real.rpow_one]
  have hL := log_pos' hx
  have h1 := log_lt_self hx
  have h2 := div_lt_log hx
  have hp : 0 < 1 + x := by linarith
  constructor
  · rw [one_lt_div hL]; exact h1
  · rw [div_le_iff₀ hL]
    rw [div_lt_iff₀ hp] at h2
    nlinarith

/-- a > 1 でも使える評価：K(x) ≤ x^(a−1)(1+x)。 -/
theorem K_le_of_one_lt {a x : ℝ} (hx : 0 < x) : K a x ≤ x ^ (a - 1) * (1 + x) := by
  unfold K
  have hL := log_pos' hx
  have h2 := div_lt_log hx
  have hp : 0 < 1 + x := by linarith
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  rw [div_le_iff₀ hL, Real.rpow_sub_one hx.ne']
  calc x ^ a = x ^ a / x * (1 + x) * (x / (1 + x)) := by field_simp
    _ ≤ x ^ a / x * (1 + x) * log (1 + x) := by
        apply mul_le_mul_of_nonneg_left h2.le (by positivity)

/-- a > 1：箱を増やす（x → 0⁺）ほど K は 0 に近づく。 -/
theorem K_tendsto_zero {a : ℝ} (ha : 1 < a) :
    Filter.Tendsto (K a) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hc : ContinuousAt (fun x : ℝ => x ^ (a - 1) * (1 + x)) 0 :=
    (Real.continuousAt_rpow_const 0 (a - 1) (Or.inr (by linarith))).mul
      (continuousAt_const.add continuousAt_id)
  have hlim : Filter.Tendsto (fun x : ℝ => x ^ (a - 1) * (1 + x)) (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
    have := hc.tendsto
    rw [Real.zero_rpow (by linarith), zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with x hx
    unfold K
    have := log_pos' hx.out
    have := Real.rpow_pos_of_pos hx.out a
    positivity
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact K_le_of_one_lt hx.out

/-! ## (4) 整数の箱の数では比例が崩れる -/

/-- a = 0.6・残り 10^(−30) で、箱 N 個の費用 N·(10^(30/N) − 1)^0.6。 -/
noncomputable def cost (N : ℕ) : ℝ := N * ((10 : ℝ) ^ ((30 : ℝ) / N) - 1) ^ (3 / 5 : ℝ)

theorem rpow35_pow5 {u : ℝ} (hu : 0 ≤ u) : (u ^ (3 / 5 : ℝ)) ^ (5 : ℕ) = u ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num

/-- 61 個の方が 60 個より安い。 -/
theorem cost61_lt_cost60 : cost 61 < cost 60 := by
  unfold cost
  set y := (10 : ℝ) ^ ((30 : ℝ) / ((61 : ℕ) : ℝ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have hy61 : y ^ (61 : ℕ) = 10 ^ (30 : ℕ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hyub : y < 31032 / 10000 := by
    by_contra hc
    push Not at hc
    have := pow_le_pow_left₀ (by norm_num) hc 61
    rw [hy61] at this
    norm_num at this
  have hy1 : 1 < y := by
    by_contra hc; push Not at hc
    have := pow_le_one₀ hy0.le hc (n := 61)
    rw [hy61] at this; norm_num at this
  have h60 : (10 : ℝ) ^ ((30 : ℝ) / ((60 : ℕ) : ℝ)) = √10 := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [h60]
  have hs : (316227 / 100000 : ℝ) < √10 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hu0 : 0 < y - 1 := by linarith
  have hA : (y - 1) ^ (3 / 5 : ℝ) < (21032 / 10000 : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_lt_rpow hu0.le (by linarith) (by norm_num)
  have hB : (216227 / 100000 : ℝ) ^ (3 / 5 : ℝ) < (√10 - 1) ^ (3 / 5 : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
  set A' := (21032 / 10000 : ℝ) ^ (3 / 5 : ℝ)
  set B' := (216227 / 100000 : ℝ) ^ (3 / 5 : ℝ)
  have hA0 : 0 ≤ A' := Real.rpow_nonneg (by norm_num) _
  have hB0 : 0 ≤ B' := Real.rpow_nonneg (by norm_num) _
  have hA5 : A' ^ (5 : ℕ) = (21032 / 10000 : ℝ) ^ (3 : ℕ) := rpow35_pow5 (by norm_num)
  have hB5 : B' ^ (5 : ℕ) = (216227 / 100000 : ℝ) ^ (3 : ℕ) := rpow35_pow5 (by norm_num)
  have hkey : 61 * A' < 60 * B' := by
    have h5 : (61 * A') ^ (5 : ℕ) < (60 * B') ^ (5 : ℕ) := by
      rw [mul_pow, mul_pow, hA5, hB5]; norm_num
    exact lt_of_pow_lt_pow_left₀ 5 (by positivity) h5
  push_cast
  nlinarith

end Paper960

end Yamagishi
