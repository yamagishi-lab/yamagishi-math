/-
論文461『向きを逆にするだけで、出口が相手を追い越す』の格上げ（一般の形）。

日本語：熱容量流量比 0 < C_r < 1 の熱交換器で、並流が NTU をどれだけ大きくしても届かない上限
1/(1 + C_r) に、対向流はちょうど NTU* = ln(1/C_r)/(1 − C_r) で届き、そこから先で出口が相手を追い越す。
NTU* は 2/(1 + C_r) と 1/√C_r のあいだにあり、C_r について狭義に減る。
English: For capacity ratio 0 < C_r < 1, counterflow reaches the parallel-flow ceiling 1/(1 + C_r)
exactly at NTU* = ln(1/C_r)/(1 − C_r), and beyond it the outlets cross; NTU* lies strictly between
2/(1 + C_r) and 1/√C_r and is strictly decreasing in C_r.

原稿（461_yamagishi_reverse_the_direction_and_the_outlet_overtakes/…_jp.tex）は、C_r = 1・入口 90 度と
20 度・NTU = 2 の一組で、並流 0.4908、対向流 0.6667、出口の四つの温度を出し、NTU = 10⁶ で並流 0.5、
二分法で対向流が NTU = 0.9996 で上限に達すると書く。一般の C_r は観察 4.7 で上限 1/(1 + C_r) を名指すだけ。

ここで証明した言明（有効度の式は ε-NTU 法の模型の式として定義に置いた）：
  (1) `effPar_lt`・`effPar_strictMono`・`effPar_tendsto`：並流 ε∥ = (1 − e^(−N(1+c)))/(1 + c) は
      N について狭義に増え、上限 1/(1 + c) に近づくが、どの N でも届かない（c ≥ 0）。
  (2) `effCounter_strictMonoOn`・`effCounter_tendsto`：対向流 ε = (1 − x)/(1 − cx)、x = e^(−N(1−c))
      は N ≥ 0 で狭義に増え、1 に近づく（0 < c < 1）。
      `effCounter_eq_iff`：ε = 1/(1 + c) ⇔ N = NTU* = ln(1/c)/(1 − c)。
      `effCounter_gt_iff`：ε > 1/(1 + c) ⇔ N > NTU*。
  (3) `ntuStar_lower`・`ntuStar_upper`：2/(1 + c) < NTU* < 1/√c（対数平均の不等式）。
      `ntuStar_gt_one`：NTU* > 1。`ntuStar_strictAntiOn`：NTU* は c について狭義に減る。
      `ntuStar_tendsto_one`：c → 1 で NTU* → 1。
  (4) c = 1 の場合：`effOne_eq_half_iff`：N/(1 + N) = 1/2 ⇔ N = 1。`counter_gt_par_one`：すべての N > 0
      で N/(1 + N) > (1 − e^(−2N))/2。
  (5) `overtake_iff`：熱容量流量 C_c, C_h > 0 のどちらが小さくても、冷側の出口が温側の出口を追い越す
      ⇔ ε > 1/(1 + C_r)。`par_never_overtakes`：並流では決して追い越さない。
      `counter_overtakes_iff`：対向流で追い越す ⇔ N > NTU*。
足した仮定：比熱一定・総括伝熱係数一定・相変化なし（原稿と同じ ε-NTU 法の模型）。
形式化していないもの：有効度の式を温度の微分方程式から出す所、0 < c < 1 で対向流が並流より大きいこと
（c = 1 だけ示した）、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper461

open Real Set Filter Topology

/-! ### 道具：対数の下からの評価 -/

/-- t > 1 で 2(t − 1)/(t + 1) < ln t。 -/
theorem two_mul_div_lt_log {t : ℝ} (ht : 1 < t) : 2 * (t - 1) / (t + 1) < log t := by
  let f : ℝ → ℝ := fun s => log s - 2 * (s - 1) / (s + 1)
  have hd : ∀ s, 0 < s → HasDerivAt f (1 / s - 4 / (s + 1) ^ 2) s := by
    intro s hs
    have h1 := hasDerivAt_log hs.ne'
    have h2 := (((hasDerivAt_id' s).sub_const 1).const_mul 2).div
      ((hasDerivAt_id' s).add_const 1) (by linarith)
    convert h1.sub h2 using 1
    field_simp
    ring
  have hf : StrictMonoOn f (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · intro s hs
      simp only [mem_Ici] at hs
      exact (hd s (by linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici, mem_Ioi] at hs
      rw [(hd s (by linarith)).deriv]
      have e : 1 / s - 4 / (s + 1) ^ 2 = (s - 1) ^ 2 / (s * (s + 1) ^ 2) := by
        field_simp; ring
      rw [e]
      apply div_pos (by nlinarith) (by positivity)
  have := hf (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
  simp only [f, log_one] at this
  linarith

/-! ### (1) 並流 -/

/-- 並流の有効度。 -/
noncomputable def effPar (c N : ℝ) : ℝ := (1 - exp (-(N * (1 + c)))) / (1 + c)

theorem effPar_lt {c : ℝ} (hc : 0 ≤ c) (N : ℝ) : effPar c N < 1 / (1 + c) := by
  unfold effPar
  apply div_lt_div_of_pos_right _ (by linarith)
  linarith [exp_pos (-(N * (1 + c)))]

theorem effPar_strictMono {c : ℝ} (hc : 0 ≤ c) : StrictMono (effPar c) := by
  intro N₁ N₂ h
  unfold effPar
  apply div_lt_div_of_pos_right _ (by linarith)
  have : exp (-(N₂ * (1 + c))) < exp (-(N₁ * (1 + c))) := exp_lt_exp.mpr (by nlinarith)
  linarith

theorem effPar_tendsto {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (effPar c) atTop (𝓝 (1 / (1 + c))) := by
  have h : Tendsto (fun N : ℝ => exp (-(N * (1 + c)))) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const (by linarith))
  have key : Tendsto (effPar c) atTop (𝓝 ((1 - 0) / (1 + c))) := (h.const_sub 1).div_const (1 + c)
  rw [sub_zero] at key
  exact key

/-! ### (2) 対向流（0 < c < 1） -/

/-- 対向流の有効度（c ≠ 1）。 -/
noncomputable def effCounter (c N : ℝ) : ℝ :=
  (1 - exp (-(N * (1 - c)))) / (1 - c * exp (-(N * (1 - c))))

/-- 上限に届く NTU*。 -/
noncomputable def ntuStar (c : ℝ) : ℝ := log (1 / c) / (1 - c)

theorem x_le_one {c N : ℝ} (hc1 : c < 1) (hN : 0 ≤ N) : exp (-(N * (1 - c))) ≤ 1 := by
  rw [exp_le_one_iff]; nlinarith

theorem denom_pos {c N : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hN : 0 ≤ N) :
    0 < 1 - c * exp (-(N * (1 - c))) := by
  have := x_le_one hc1 hN
  nlinarith [exp_pos (-(N * (1 - c)))]

/-- x の関数として見た対向流の有効度は、x について狭義に減る。 -/
theorem g_strictAnti {c x₁ x₂ : ℝ} (hc1 : c < 1) (h1 : 0 < 1 - c * x₁) (h2 : 0 < 1 - c * x₂)
    (h : x₁ < x₂) : (1 - x₂) / (1 - c * x₂) < (1 - x₁) / (1 - c * x₁) := by
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

theorem effCounter_strictMonoOn {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    StrictMonoOn (effCounter c) (Ici 0) := by
  intro N₁ h₁ N₂ h₂ h
  simp only [mem_Ici] at h₁ h₂
  unfold effCounter
  apply g_strictAnti hc1 (denom_pos hc0 hc1 h₂) (denom_pos hc0 hc1 h₁)
  exact exp_lt_exp.mpr (by nlinarith)

theorem effCounter_tendsto {c : ℝ} (hc1 : c < 1) :
    Tendsto (effCounter c) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℝ => exp (-(N * (1 - c)))) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const (by linarith))
  have key : Tendsto (effCounter c) atTop (𝓝 ((1 - 0) / (1 - c * 0))) :=
    (h.const_sub 1).div ((h.const_mul c).const_sub 1) (by norm_num)
  norm_num at key
  exact key

/-- (2) 対向流が上限 1/(1 + c) に届く ⇔ N = NTU*。 -/
theorem effCounter_eq_iff {c N : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hN : 0 ≤ N) :
    effCounter c N = 1 / (1 + c) ↔ N = ntuStar c := by
  have hD := denom_pos hc0 hc1 hN
  unfold effCounter ntuStar
  rw [div_eq_div_iff hD.ne' (by linarith)]
  have h1c : (1 : ℝ) - c ≠ 0 := by linarith
  constructor
  · intro h
    have hx : exp (-(N * (1 - c))) = c := by linarith
    have := congrArg log hx
    rw [log_exp] at this
    rw [one_div, log_inv, eq_div_iff h1c]
    linarith
  · intro h
    have hx : exp (-(N * (1 - c))) = c := by
      rw [h, one_div, log_inv, div_mul_cancel₀ _ h1c, neg_neg, exp_log hc0]
    rw [hx]; ring

theorem ntuStar_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : 0 < ntuStar c := by
  unfold ntuStar
  apply div_pos _ (by linarith)
  apply log_pos; rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hc0, hc1⟩

/-- (2) ε > 1/(1 + c) ⇔ N > NTU*。 -/
theorem effCounter_gt_iff {c N : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hN : 0 ≤ N) :
    1 / (1 + c) < effCounter c N ↔ ntuStar c < N := by
  have hS := ntuStar_pos hc0 hc1
  have heq : effCounter c (ntuStar c) = 1 / (1 + c) :=
    (effCounter_eq_iff hc0 hc1 hS.le).mpr rfl
  have hm := effCounter_strictMonoOn hc0 hc1
  constructor
  · intro h
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | he
    · have := hm (mem_Ici.mpr hN) (mem_Ici.mpr hS.le) hlt
      linarith
    · rw [he] at h; linarith
  · intro h
    have := hm (mem_Ici.mpr hS.le) (mem_Ici.mpr hN) h
    linarith

/-! ### (3) NTU* の範囲と単調性 -/

/-- (3) 下の限界 2/(1 + c) < NTU*（対数平均 < 算術平均）。 -/
theorem ntuStar_lower {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : 2 / (1 + c) < ntuStar c := by
  unfold ntuStar
  have ht : 1 < 1 / c := by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hc0, hc1⟩
  have key := two_mul_div_lt_log ht
  have e : 2 * (1 / c - 1) / (1 / c + 1) = 2 * (1 - c) / (1 + c) := by
    field_simp
  rw [e] at key
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have : 2 * (1 - c) / (1 + c) * (1 + c) = 2 * (1 - c) := by field_simp
  nlinarith

/-- (3) 上の限界 NTU* < 1/√c（幾何平均 < 対数平均）。 -/
theorem ntuStar_upper {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : ntuStar c < 1 / √c := by
  unfold ntuStar
  have hs : 0 < √c := sqrt_pos.mpr hc0
  have hs1 : √c < 1 := by rw [sqrt_lt' (by norm_num)]; linarith
  set y := 1 / √c with hy
  have hy1 : 1 < y := by rw [hy, one_div]; exact one_lt_inv_iff₀.mpr ⟨hs, hs1⟩
  have hy0 : 0 < y := by linarith
  have hl : 0 < log y := log_pos hy1
  have key := (self_lt_sinh_iff (x := log y)).mpr hl
  rw [sinh_eq, exp_neg, exp_log hy0] at key
  have hc : c = 1 / y ^ 2 := by
    rw [hy]; field_simp; rw [sq_sqrt hc0.le]
  have hlog : log (1 / c) = 2 * log y := by
    rw [hc, one_div_one_div, log_pow]; push_cast; ring
  rw [hlog, hc, div_lt_iff₀ (by
    have : y ^ 2 > 1 := by nlinarith
    rw [sub_pos, div_lt_one (by positivity)]; linarith)]
  have e : y * (1 - 1 / y ^ 2) = y - y⁻¹ := by field_simp
  rw [e]
  linarith

/-- (3) NTU* > 1。 -/
theorem ntuStar_gt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) : 1 < ntuStar c := by
  have h := ntuStar_lower hc0 hc1
  have : 1 < 2 / (1 + c) := by rw [lt_div_iff₀ (by linarith)]; linarith
  linarith

/-- (3) NTU* は c について狭義に減る。 -/
theorem ntuStar_strictAntiOn : StrictAntiOn ntuStar (Ioo 0 1) := by
  have hd : ∀ c ∈ Ioo (0 : ℝ) 1,
      HasDerivAt ntuStar ((log (1 / c) - (1 / c - 1)) / (1 - c) ^ 2) c := by
    intro c hc
    obtain ⟨hc0, hc1⟩ := hc
    have h1 : HasDerivAt (fun x => log (1 / x)) (-(1 / c)) c := by
      have := (hasDerivAt_log hc0.ne').neg
      convert this using 1
      · funext x; simp [one_div, log_inv]
      · rw [one_div]
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) c := by
      simpa using (hasDerivAt_id' c).const_sub 1
    have := h1.div h2 (by linarith)
    unfold ntuStar
    convert this using 1
    have : (1 : ℝ) - c ≠ 0 := by linarith
    field_simp
    ring
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro c hc
    exact (hd c hc).continuousAt.continuousWithinAt
  · intro c hc
    rw [interior_Ioo] at hc
    rw [(hd c hc).deriv]
    obtain ⟨hc0, hc1⟩ := hc
    apply div_neg_of_neg_of_pos _ (by nlinarith)
    have h1c : 1 / c ≠ 1 := by
      rw [ne_eq, div_eq_one_iff_eq hc0.ne']; intro h; linarith
    have := log_lt_sub_one_of_pos (by positivity) h1c
    linarith

/-- (3) c → 1 で NTU* → 1。 -/
theorem ntuStar_tendsto_one : Tendsto ntuStar (𝓝[<] 1) (𝓝 1) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_log (x := (1 : ℝ)) one_ne_zero))
  have h' : Tendsto (slope log 1) (𝓝[<] 1) (𝓝 1) := by
    simpa using h.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_lt hx))
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [slope_def_field, ntuStar, log_one, one_div, log_inv]
  have : c - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hc)
  have : (1 : ℝ) - c ≠ 0 := by intro h; apply this; linarith
  field_simp
  ring

/-! ### (4) c = 1 -/

/-- c = 1 の対向流の有効度 N/(1 + N)。 -/
noncomputable def effOne (N : ℝ) : ℝ := N / (1 + N)

/-- (4) N/(1 + N) = 1/2 ⇔ N = 1（原稿の 0.9996 は目標 0.4999 の値で、ちょうど届くのは 1）。 -/
theorem effOne_eq_half_iff {N : ℝ} (hN : 0 ≤ N) : effOne N = 1 / 2 ↔ N = 1 := by
  unfold effOne
  rw [div_eq_div_iff (by linarith) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- (4) c = 1 で、すべての N > 0 について対向流 > 並流。 -/
theorem counter_gt_par_one {N : ℝ} (hN : 0 < N) : effPar 1 N < effOne N := by
  unfold effPar effOne
  rw [show (1 : ℝ) + 1 = 2 by norm_num, div_lt_div_iff₀ (by norm_num) (by linarith)]
  -- (1 − e^(−2N))(1 + N) < 2N ⇔ (1 − N) < (1 + N) e^(−2N)
  have ht : 1 < exp (2 * N) := one_lt_exp_iff.mpr (by linarith)
  have key := two_mul_div_lt_log ht
  rw [log_exp] at key
  have hE : exp (-(N * 2)) = (exp (2 * N))⁻¹ := by rw [← exp_neg]; ring_nf
  rw [hE]
  set E := exp (2 * N) with hEdef
  have hE0 : 0 < E := exp_pos _
  rw [div_lt_iff₀ (by linarith)] at key
  have : (1 - E⁻¹) * (1 + N) * E = (E - 1) * (1 + N) := by field_simp
  have h2 : (1 - E⁻¹) * (1 + N) < N * 2 := by
    by_contra hc
    push Not at hc
    have := mul_le_mul_of_nonneg_right hc hE0.le
    nlinarith
  linarith

/-! ### (5) 出口の追い越し -/

/-- (5) 冷側の出口が温側の出口を追い越す ⇔ ε > 1/(1 + C_r)。熱の量 Q = ε·C_min·(T_h − T_c)。 -/
theorem overtake_iff {Cc Ch Th Tc ε : ℝ} (hCc : 0 < Cc) (hCh : 0 < Ch) (hT : Tc < Th) :
    Th - ε * min Cc Ch * (Th - Tc) / Ch < Tc + ε * min Cc Ch * (Th - Tc) / Cc ↔
      1 / (1 + min Cc Ch / max Cc Ch) < ε := by
  have hD : 0 < Th - Tc := by linarith
  rcases le_total Cc Ch with h | h
  · rw [min_eq_left h, max_eq_right h]
    rw [div_lt_iff₀ (by positivity)]
    have e1 : Tc + ε * Cc * (Th - Tc) / Cc = Tc + ε * (Th - Tc) := by field_simp
    rw [e1]
    have e2 : ε * Cc * (Th - Tc) / Ch = ε * (Cc / Ch) * (Th - Tc) := by ring
    rw [e2]
    constructor
    · intro h1; nlinarith
    · intro h1; nlinarith
  · rw [min_eq_right h, max_eq_left h]
    rw [div_lt_iff₀ (by positivity)]
    have e1 : ε * Ch * (Th - Tc) / Ch = ε * (Th - Tc) := by field_simp
    rw [e1]
    have e2 : ε * Ch * (Th - Tc) / Cc = ε * (Ch / Cc) * (Th - Tc) := by ring
    rw [e2]
    constructor
    · intro h1; nlinarith
    · intro h1; nlinarith

/-- (5) 並流では、どの N でも出口は追い越さない。 -/
theorem par_never_overtakes {Cc Ch Th Tc : ℝ} (hCc : 0 < Cc) (hCh : 0 < Ch) (hT : Tc < Th)
    (N : ℝ) :
    let ε := effPar (min Cc Ch / max Cc Ch) N
    ¬ (Th - ε * min Cc Ch * (Th - Tc) / Ch < Tc + ε * min Cc Ch * (Th - Tc) / Cc) := by
  intro ε
  rw [overtake_iff hCc hCh hT, not_lt]
  exact (effPar_lt (by positivity) N).le

/-- (5) 対向流（0 < C_r < 1）で出口が追い越す ⇔ N > NTU*。 -/
theorem counter_overtakes_iff {Cc Ch Th Tc N : ℝ} (hCc : 0 < Cc) (hCh : 0 < Ch) (hT : Tc < Th)
    (hne : Cc ≠ Ch) (hN : 0 ≤ N) :
    let c := min Cc Ch / max Cc Ch
    let ε := effCounter c N
    (Th - ε * min Cc Ch * (Th - Tc) / Ch < Tc + ε * min Cc Ch * (Th - Tc) / Cc ↔
      ntuStar c < N) := by
  intro c ε
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    have hmax : 0 < max Cc Ch := lt_max_of_lt_left hCc
    show min Cc Ch / max Cc Ch < 1
    rw [div_lt_one hmax]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  rw [overtake_iff hCc hCh hT]
  exact effCounter_gt_iff hc0 hc1 hN

end Paper461

end Yamagishi
