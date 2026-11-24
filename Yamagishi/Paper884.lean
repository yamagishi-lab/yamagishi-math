/-
論文884『GI が食品の速さを表すのは 2 時間で区切るからで、区切らなければ面積は炭水化物の量だけで決まる』の
格上げ（一般の形）。

日本語の一文：一次の吸収（速さ k_a）と一次の消失（k_e）の二つの箱で、区切り T までの血糖の面積の比
GI_T = 100·A_{k_a}(T)/A_{k_g}(T) は、どの k_e でも、どの T でも吸収の速さについて狭義に増え、
k_a < k_g なら T について狭義に増えて、T → ∞ で 100 に、T → 0 で 100·k_a/k_g に近づく。
English: In the two-compartment model with first-order absorption k_a and elimination k_e, the area
ratio GI_T = 100·A_{k_a}(T)/A_{k_g}(T) is, for every k_e and every cut T, strictly increasing in the
absorption rate; for k_a < k_g it is strictly increasing in T, tends to 100 as T → ∞ and to
100·k_a/k_g as T → 0.

原稿（884_yamagishi_gi_reflects_speed_only_because_of_the_cut/…_jp.tex）は、k_e = 1、ぶどう糖
k_a = 6 で、k_a = 6・3・1.5・0.75・0.4 の五つの食品を T = 2・4・8 時間と区切らない場合で表にしている。
区切らない面積 D/k_e は一般の式で示しているが、T と k_a についての単調性と端の値は表だけ。

ここで証明した言明（D, k_e > 0、吸収の速さ k > 0、J(c, t) = ∫₀ᵗ e^(cs) ds）：
  (1) `gut_deriv`・`blood_deriv`：胃腸の量 G(t) = D e^(−kt) と血糖の上がり B(t) = Dk e^(−k_e t) J(k_e − k, t)
      は、模型の式 G′ = −kG、B′ = kG − k_e B と G(0) = D、B(0) = 0 を満たす。
      `area_closed`：面積 A_k(T) = ∫₀ᵀ B は D[(1 − e^(−k_e T))/k_e − e^(−k_e T) J(k_e − k, T)]。
  (2) `area_strictMono_k`：T > 0 で A_k(T) は k について狭義に増える（食品の順は区切りによらない）。
  (3) `blood_cross`：k_a < k_g、0 < t < T なら B_g(T)B_a(t) < B_a(T)B_g(t)（芯は `J_ratio`）。
      `GI_strictMonoOn`：k_a < k_g なら A_a(T)/A_g(T) は T について狭義に増える。
      `GI_strictAntiOn`：k_a > k_g なら狭義に減る。
  (4) `area_tendsto`：T → ∞ で A_k(T) → D/k_e（区切らない面積は吸収の速さによらない）。
      `GI_tendsto_atTop`：A_a/A_g → 1。`GI_tendsto_zero`：T → 0 で A_a/A_g → k_a/k_g。
足した仮定：全部が吸収されること、一次の吸収と一次の消失の二つの箱（原稿と同じ）を定義に置いた。
吸収される割合 F が食品で違えば T → ∞ の GI は 100F になる（ここでは F = 1）。
形式化していないもの：原稿の数表・GL・山の高さ、体の非線形、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper884

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- J(c, t) = ∫₀ᵗ e^(cs) ds。 -/
noncomputable def J (c t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, exp (c * s)

theorem continuous_expc (c : ℝ) : Continuous (fun s => exp (c * s)) :=
  (continuous_const.mul continuous_id).rexp

theorem hasDerivAt_J (c t : ℝ) : HasDerivAt (J c) (exp (c * t)) t :=
  ((continuous_expc c).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem continuous_J (c : ℝ) : Continuous (J c) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_J c t).continuousAt

theorem J_zero (c : ℝ) : J c 0 = 0 := by simp [J]

/-- c·J(c, t) = e^(ct) − 1（c = 0 も含む）。 -/
theorem cJ_eq (c t : ℝ) : c * J c t = exp (c * t) - 1 := by
  have hd : ∀ x, HasDerivAt (fun x => c * J c x - exp (c * x) + 1) 0 x := by
    intro x
    have h1 := (hasDerivAt_J c x).const_mul c
    have h2 : HasDerivAt (fun x => exp (c * x)) (exp (c * x) * (c * 1)) x :=
      ((hasDerivAt_id' x).const_mul c).exp
    have := (h1.sub h2).add_const 1
    refine this.congr_deriv ?_
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0
  simp only [J_zero, mul_zero, exp_zero] at hc
  linarith

theorem J_pos {c t : ℝ} (ht : 0 < t) : 0 < J c t :=
  intervalIntegral_pos_of_pos_on ((continuous_expc c).intervalIntegrable 0 t)
    (fun _ _ => exp_pos _) ht

/-- J は c について狭義に増える（t > 0）。 -/
theorem J_strictMono_c {c1 c2 t : ℝ} (ht : 0 < t) (hc : c1 < c2) : J c1 t < J c2 t := by
  unfold J
  apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (continuous_expc c1).continuousOn (continuous_expc c2).continuousOn
  · intro s hs
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc.le (le_of_lt hs.1))
  · exact ⟨t, ⟨ht.le, le_rfl⟩, exp_lt_exp.mpr (mul_lt_mul_of_pos_right hc ht)⟩

/-! ### 模型 -/

/-- 胃腸に残る量 G(t) = D e^(−kt)。 -/
noncomputable def gut (D k t : ℝ) : ℝ := D * exp (-k * t)

/-- 血糖の上がり B(t) = Dk e^(−k_e t) J(k_e − k, t)。 -/
noncomputable def blood (D e k t : ℝ) : ℝ := D * k * (exp (-e * t) * J (e - k) t)

/-- 区切り T までの面積 A_k(T) = ∫₀ᵀ B。 -/
noncomputable def area (D e k T : ℝ) : ℝ := ∫ t in (0 : ℝ)..T, blood D e k t

theorem gut_deriv (D k t : ℝ) : HasDerivAt (gut D k) (-k * gut D k t) t := by
  have := (((hasDerivAt_id' t).const_mul (-k)).exp).const_mul D
  unfold gut
  refine this.congr_deriv ?_
  ring

theorem blood_zero (D e k : ℝ) : blood D e k 0 = 0 := by simp [blood, J_zero]

theorem blood_deriv (D e k t : ℝ) :
    HasDerivAt (blood D e k) (k * gut D k t - e * blood D e k t) t := by
  have h1 : HasDerivAt (fun t => exp (-e * t)) (exp (-e * t) * (-e * 1)) t :=
    ((hasDerivAt_id' t).const_mul (-e)).exp
  have h2 : HasDerivAt (fun t => exp (-e * t) * J (e - k) t)
      (exp (-e * t) * (-e * 1) * J (e - k) t + exp (-e * t) * exp ((e - k) * t)) t :=
    h1.mul (hasDerivAt_J (e - k) t)
  have := h2.const_mul (D * k)
  unfold blood
  refine this.congr_deriv ?_
  unfold gut
  have : exp (-e * t) * exp ((e - k) * t) = exp (-k * t) := by rw [← exp_add]; ring_nf
  rw [← this]
  ring

theorem continuous_blood (D e k : ℝ) : Continuous (blood D e k) :=
  continuous_iff_continuousAt.mpr fun t => (blood_deriv D e k t).continuousAt

theorem blood_pos {D e k t : ℝ} (hD : 0 < D) (hk : 0 < k) (ht : 0 < t) : 0 < blood D e k t := by
  unfold blood
  have := J_pos (c := e - k) ht
  positivity

theorem hasDerivAt_area (D e k T : ℝ) : HasDerivAt (area D e k) (blood D e k T) T :=
  ((continuous_blood D e k).integral_hasStrictDerivAt 0 T).hasDerivAt

theorem area_pos {D e k T : ℝ} (hD : 0 < D) (hk : 0 < k) (hT : 0 < T) : 0 < area D e k T :=
  intervalIntegral_pos_of_pos_on ((continuous_blood D e k).intervalIntegrable 0 T)
    (fun _ ht => blood_pos hD hk ht.1) hT

/-- (1) 面積の閉じた形。 -/
theorem area_closed {D e k : ℝ} (he : 0 < e) (T : ℝ) :
    area D e k T = D * ((1 - exp (-e * T)) / e - exp (-e * T) * J (e - k) T) := by
  set G := fun T => D * ((1 - exp (-e * T)) / e - exp (-e * T) * J (e - k) T) with hG
  have hd : ∀ x, HasDerivAt G (blood D e k x) x := by
    intro x
    have h1 : HasDerivAt (fun t => exp (-e * t)) (exp (-e * x) * (-e * 1)) x :=
      ((hasDerivAt_id' x).const_mul (-e)).exp
    have := ((((hasDerivAt_const x (1 : ℝ)).sub h1).div_const e).sub
      (h1.mul (hasDerivAt_J (e - k) x))).const_mul D
    refine this.congr_deriv ?_
    unfold blood
    have hc := cJ_eq (e - k) x
    have hne : e ≠ 0 := ne_of_gt he
    rw [show (0 - exp (-e * x) * (-e * 1)) / e = exp (-e * x) by field_simp; ring]
    linear_combination (D * exp (-e * x)) * hc
  have hint : IntervalIntegrable (blood D e k) volume 0 T :=
    (continuous_blood D e k).intervalIntegrable 0 T
  unfold area
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hint]
  simp [hG, J_zero]

/-- (2) T > 0 で A_k(T) は k について狭義に増える。 -/
theorem area_strictMono_k {D e k1 k2 T : ℝ} (hD : 0 < D) (he : 0 < e) (hT : 0 < T)
    (hk : k1 < k2) : area D e k1 T < area D e k2 T := by
  rw [area_closed he, area_closed he]
  have := J_strictMono_c (t := T) hT (show e - k2 < e - k1 by linarith)
  have hE := exp_pos (-e * T)
  have : exp (-e * T) * J (e - k2) T < exp (-e * T) * J (e - k1) T :=
    mul_lt_mul_of_pos_left this hE
  nlinarith

/-! ### 区切りについての単調性 -/

/-- 芯：c₂ < c₁、0 < t < T なら J(c₁, t)J(c₂, T) < J(c₂, t)J(c₁, T)。 -/
theorem J_ratio {c1 c2 t T : ℝ} (hc : c2 < c1) (ht : 0 < t) (htT : t < T) :
    J c1 t * J c2 T < J c2 t * J c1 T := by
  set δ := c1 - c2 with hδ
  have hδ0 : 0 < δ := by linarith
  set E := exp (δ * t) with hE
  have hE1 : 1 < E := by rw [hE, ← exp_zero]; exact exp_lt_exp.mpr (by positivity)
  -- 区間を [0, t] と [t, T] に分ける
  have hsplit : ∀ c, J c T = J c t + ∫ s in t..T, exp (c * s) := by
    intro c
    unfold J
    rw [integral_add_adjacent_intervals ((continuous_expc c).intervalIntegrable 0 t)
      ((continuous_expc c).intervalIntegrable t T)]
  -- [0, t] で e^(c₁s) ≤ E e^(c₂s)、s = 0 で真に小さい
  have hlow : J c1 t < E * J c2 t := by
    unfold J
    rw [← intervalIntegral.integral_const_mul]
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
      (continuous_expc c1).continuousOn ((continuous_expc c2).const_mul E).continuousOn
    · intro s hs
      rw [hE, ← exp_add]
      apply exp_le_exp.mpr
      have : δ * s ≤ δ * t := mul_le_mul_of_nonneg_left hs.2 hδ0.le
      linarith
    · refine ⟨0, ⟨le_rfl, ht.le⟩, ?_⟩
      simp only [mul_zero, exp_zero, mul_one]
      exact hE1
  -- [t, T] で e^(c₁s) ≥ E e^(c₂s)、s = T で真に大きい
  have hhigh : E * ∫ s in t..T, exp (c2 * s) < ∫ s in t..T, exp (c1 * s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt htT
      ((continuous_expc c2).const_mul E).continuousOn (continuous_expc c1).continuousOn
    · intro s hs
      rw [hE, ← exp_add]
      apply exp_le_exp.mpr
      have : δ * t ≤ δ * s := mul_le_mul_of_nonneg_left hs.1.le hδ0.le
      linarith
    · refine ⟨T, ⟨htT.le, le_rfl⟩, ?_⟩
      rw [hE, ← exp_add]
      apply exp_lt_exp.mpr
      have : δ * t < δ * T := mul_lt_mul_of_pos_left htT hδ0
      linarith
  have hK2 : 0 < ∫ s in t..T, exp (c2 * s) :=
    intervalIntegral_pos_of_pos_on ((continuous_expc c2).intervalIntegrable t T)
      (fun _ _ => exp_pos _) htT
  have hJ2 := J_pos (c := c2) ht
  rw [hsplit c2, hsplit c1]
  have h1 : J c1 t * (∫ s in t..T, exp (c2 * s)) <
      E * J c2 t * (∫ s in t..T, exp (c2 * s)) := mul_lt_mul_of_pos_right hlow hK2
  have h2 : J c2 t * (E * ∫ s in t..T, exp (c2 * s)) <
      J c2 t * (∫ s in t..T, exp (c1 * s)) := mul_lt_mul_of_pos_left hhigh hJ2
  nlinarith

/-- (3) k_a < k_g、0 < t < T なら B_g(T)B_a(t) < B_a(T)B_g(t)。 -/
theorem blood_cross {D e ka kg t T : ℝ} (hD : 0 < D) (hka : 0 < ka) (hkg : ka < kg)
    (ht : 0 < t) (htT : t < T) :
    blood D e kg T * blood D e ka t < blood D e ka T * blood D e kg t := by
  have hkg0 : 0 < kg := hka.trans hkg
  have hJ := J_ratio (c1 := e - ka) (c2 := e - kg) (by linarith) ht htT
  unfold blood
  have hpos : 0 < D * ka * exp (-e * T) * (D * kg * exp (-e * t)) := by positivity
  have := mul_lt_mul_of_pos_left hJ hpos
  nlinarith

/-- 区切りでの面積の比 A_a(T)/A_g(T)（GI_T/100）。 -/
noncomputable def GI (D e ka kg T : ℝ) : ℝ := area D e ka T / area D e kg T

/-- (3) B_a(T)A_g(T) − A_a(T)B_g(T) > 0（k_a < k_g、T > 0）。 -/
theorem cross_area {D e ka kg T : ℝ} (hD : 0 < D) (hka : 0 < ka) (hkg : ka < kg)
    (hT : 0 < T) :
    area D e ka T * blood D e kg T < blood D e ka T * area D e kg T := by
  unfold area
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hT
    ((continuous_blood D e ka).mul continuous_const).continuousOn
    (continuous_const.mul (continuous_blood D e kg)).continuousOn
  · intro t ht
    simp only [Pi.mul_apply]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, mul_comm]
    · have := blood_cross (e := e) hD hka hkg ht.1 h
      linarith
  · refine ⟨T / 2, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [Pi.mul_apply]
    have := blood_cross (e := e) hD hka hkg (by linarith : 0 < T / 2) (by linarith : T / 2 < T)
    linarith

/-- (3) k_a < k_g なら A_a/A_g は T について狭義に増える。 -/
theorem GI_strictMonoOn {D e ka kg : ℝ} (hD : 0 < D) (hka : 0 < ka) (hkg : ka < kg) :
    StrictMonoOn (GI D e ka kg) (Ioi 0) := by
  have hkg0 : 0 < kg := hka.trans hkg
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro T hT
    exact ((hasDerivAt_area D e ka T).continuousAt.div (hasDerivAt_area D e kg T).continuousAt
      (ne_of_gt (area_pos hD hkg0 hT))).continuousWithinAt
  · intro T hT
    rw [interior_Ioi] at hT
    have hA := area_pos (e := e) hD hkg0 hT
    have hd := (hasDerivAt_area D e ka T).div (hasDerivAt_area D e kg T) (ne_of_gt hA)
    have hd' : HasDerivAt (GI D e ka kg) _ T := hd
    rw [hd'.deriv]
    apply div_pos _ (by positivity)
    have := cross_area (e := e) hD hka hkg hT
    linarith

/-- (3) k_a > k_g なら狭義に減る。 -/
theorem GI_strictAntiOn {D e ka kg : ℝ} (hD : 0 < D) (hkg : 0 < kg) (hk : kg < ka) :
    StrictAntiOn (GI D e ka kg) (Ioi 0) := by
  have hka0 : 0 < ka := hkg.trans hk
  intro x hx y hy hxy
  have hmono := GI_strictMonoOn (e := e) hD hkg hk hx hy hxy
  unfold GI at *
  have h1 := area_pos (e := e) hD hka0 hx
  have h2 := area_pos (e := e) hD hka0 hy
  have h3 := area_pos (e := e) hD hkg hx
  have h4 := area_pos (e := e) hD hkg hy
  rw [div_lt_div_iff₀ h1 h2] at hmono
  rw [div_lt_div_iff₀ h4 h3]
  linarith

/-! ### 区切りの端 -/

/-- e^(−k_e t) J(k_e − k, t) = ∫₀ᵗ e^(−k_e t + (k_e − k)s) ds。 -/
theorem EJ_eq (e k t : ℝ) :
    exp (-e * t) * J (e - k) t = ∫ s in (0 : ℝ)..t, exp (-e * t + (e - k) * s) := by
  unfold J
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext s
  rw [← exp_add]

/-- 0 ≤ s ≤ t で −(k_e + k)t ≤ −k_e t + (k_e − k)s ≤ −min(k_e, k)·t。 -/
theorem expo_bounds {e k s t : ℝ} (he : 0 < e) (hk : 0 < k) (hs : 0 ≤ s) (hst : s ≤ t) :
    -(e + k) * t ≤ -e * t + (e - k) * s ∧ -e * t + (e - k) * s ≤ -min e k * t := by
  have h1 : min e k ≤ e := min_le_left e k
  have h2 : min e k ≤ k := min_le_right e k
  constructor
  · nlinarith
  · nlinarith

theorem EJ_le {e k t : ℝ} (he : 0 < e) (hk : 0 < k) (ht : 0 ≤ t) :
    exp (-e * t) * J (e - k) t ≤ t * exp (-min e k * t) := by
  rw [EJ_eq]
  have := intervalIntegral.integral_mono_on ht
    ((continuous_const.add (continuous_const.mul continuous_id)).rexp.intervalIntegrable
      (μ := volume) 0 t)
    (continuous_const.intervalIntegrable (μ := volume) 0 t)
    (fun s hs => exp_le_exp.mpr (expo_bounds he hk hs.1 hs.2).2)
    (f := fun s => exp (-e * t + (e - k) * s)) (g := fun _ => exp (-min e k * t))
  simpa using this

theorem EJ_ge {e k t : ℝ} (he : 0 < e) (hk : 0 < k) (ht : 0 ≤ t) :
    t * exp (-(e + k) * t) ≤ exp (-e * t) * J (e - k) t := by
  rw [EJ_eq]
  have := intervalIntegral.integral_mono_on ht
    (continuous_const.intervalIntegrable (μ := volume) 0 t)
    ((continuous_const.add (continuous_const.mul continuous_id)).rexp.intervalIntegrable
      (μ := volume) 0 t)
    (fun s hs => exp_le_exp.mpr (expo_bounds he hk hs.1 hs.2).1)
    (g := fun s => exp (-e * t + (e - k) * s)) (f := fun _ => exp (-(e + k) * t))
  simpa using this

theorem EJ_nonneg {e k t : ℝ} (ht : 0 ≤ t) : 0 ≤ exp (-e * t) * J (e - k) t := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, J_zero, mul_zero]
  · exact (mul_pos (exp_pos _) (J_pos h)).le

/-- (4) T → ∞ で A_k(T) → D/k_e。 -/
theorem area_tendsto {D e k : ℝ} (he : 0 < e) (hk : 0 < k) :
    Tendsto (area D e k) atTop (𝓝 (D / e)) := by
  have hm : 0 < min e k := lt_min he hk
  -- T e^(−mT) → 0
  have hTe : Tendsto (fun T => T * exp (-min e k * T)) atTop (𝓝 0) := by
    have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hm)
    have h2 := h.const_mul (1 / min e k)
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun T => ?_)
    simp only [Function.comp, id, pow_one]
    field_simp
  have hEJ : Tendsto (fun T => exp (-e * T) * J (e - k) T) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTe
    · filter_upwards [eventually_ge_atTop 0] with T hT using EJ_nonneg hT
    · filter_upwards [eventually_ge_atTop 0] with T hT using EJ_le he hk hT
  have hE : Tendsto (fun T => exp (-e * T)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hE).div_const e).sub hEJ).const_mul D
  simp only [sub_zero] at this
  rw [mul_one_div] at this
  refine this.congr' (Eventually.of_forall fun T => ?_)
  rw [area_closed he]

/-- (4) T → ∞ で A_a/A_g → 1。 -/
theorem GI_tendsto_atTop {D e ka kg : ℝ} (hD : 0 < D) (he : 0 < e) (hka : 0 < ka)
    (hkg : 0 < kg) : Tendsto (GI D e ka kg) atTop (𝓝 1) := by
  have := (area_tendsto (D := D) he hka).div (area_tendsto (D := D) he hkg)
    (by positivity : D / e ≠ 0)
  rw [div_self (by positivity : D / e ≠ 0)] at this
  exact this

/-- 面積の上下：Dk e^(−(k_e + k)T) T²/2 ≤ A_k(T) ≤ Dk T²/2（T ≥ 0）。 -/
theorem area_bounds {D e k T : ℝ} (hD : 0 < D) (he : 0 < e) (hk : 0 < k) (hT : 0 ≤ T) :
    D * k * exp (-(e + k) * T) * (T ^ 2 / 2) ≤ area D e k T ∧
      area D e k T ≤ D * k * (T ^ 2 / 2) := by
  have hDk : 0 < D * k := mul_pos hD hk
  have hint : IntervalIntegrable (blood D e k) volume 0 T :=
    (continuous_blood D e k).intervalIntegrable 0 T
  have hid : ∫ t in (0 : ℝ)..T, t = T ^ 2 / 2 := by simp [integral_id]
  constructor
  · have := intervalIntegral.integral_mono_on hT
      ((continuous_const.mul continuous_id).intervalIntegrable 0 T) hint
      (f := fun t => D * k * exp (-(e + k) * T) * t) (g := blood D e k)
      (fun t ht => by
        unfold blood
        have h1 := EJ_ge (e := e) (k := k) he hk ht.1
        have h2 : exp (-(e + k) * T) ≤ exp (-(e + k) * t) :=
          exp_le_exp.mpr (by nlinarith [ht.2])
        have h3 : t * exp (-(e + k) * T) ≤ t * exp (-(e + k) * t) :=
          mul_le_mul_of_nonneg_left h2 ht.1
        nlinarith)
    rw [intervalIntegral.integral_const_mul, hid] at this
    exact this
  · have := intervalIntegral.integral_mono_on hT hint
      ((continuous_const.mul continuous_id).intervalIntegrable 0 T)
      (g := fun t => D * k * t) (f := blood D e k)
      (fun t ht => by
        unfold blood
        have h1 := EJ_le (e := e) (k := k) he hk ht.1
        have h2 : exp (-min e k * t) ≤ 1 := by
          rw [exp_le_one_iff]; nlinarith [lt_min he hk, ht.1]
        have h3 : t * exp (-min e k * t) ≤ t := by nlinarith [ht.1]
        nlinarith)
    rw [intervalIntegral.integral_const_mul, hid] at this
    exact this

/-- (4) T → 0（正の側）で A_a/A_g → k_a/k_g。 -/
theorem GI_tendsto_zero {D e ka kg : ℝ} (hD : 0 < D) (he : 0 < e) (hka : 0 < ka)
    (hkg : 0 < kg) : Tendsto (GI D e ka kg) (𝓝[>] 0) (𝓝 (ka / kg)) := by
  have hlo : Tendsto (fun T => ka / kg * exp (-(e + ka) * T)) (𝓝[>] 0) (𝓝 (ka / kg)) := by
    have : Tendsto (fun T => ka / kg * exp (-(e + ka) * T)) (𝓝 0)
        (𝓝 (ka / kg * exp (-(e + ka) * 0))) :=
      ((continuous_const.mul ((continuous_const.mul continuous_id).rexp)).tendsto 0)
    simp only [mul_zero, exp_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun T => ka / kg * exp ((e + kg) * T)) (𝓝[>] 0) (𝓝 (ka / kg)) := by
    have : Tendsto (fun T => ka / kg * exp ((e + kg) * T)) (𝓝 0)
        (𝓝 (ka / kg * exp ((e + kg) * 0))) :=
      ((continuous_const.mul ((continuous_const.mul continuous_id).rexp)).tendsto 0)
    simp only [mul_zero, exp_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [self_mem_nhdsWithin] with T hT
    have hT0 : 0 < T := hT
    obtain ⟨a1, a2⟩ := area_bounds (e := e) hD he hka hT0.le
    obtain ⟨g1, g2⟩ := area_bounds (e := e) hD he hkg hT0.le
    have hg := area_pos (e := e) hD hkg hT0
    unfold GI
    rw [le_div_iff₀ hg]
    have : 0 < T ^ 2 / 2 := by positivity
    calc ka / kg * exp (-(e + ka) * T) * area D e kg T
        ≤ ka / kg * exp (-(e + ka) * T) * (D * kg * (T ^ 2 / 2)) := by
          apply mul_le_mul_of_nonneg_left g2; positivity
      _ = D * ka * exp (-(e + ka) * T) * (T ^ 2 / 2) := by field_simp
      _ ≤ area D e ka T := a1
  · filter_upwards [self_mem_nhdsWithin] with T hT
    have hT0 : 0 < T := hT
    obtain ⟨a1, a2⟩ := area_bounds (e := e) hD he hka hT0.le
    obtain ⟨g1, g2⟩ := area_bounds (e := e) hD he hkg hT0.le
    have hg := area_pos (e := e) hD hkg hT0
    unfold GI
    rw [div_le_iff₀ hg]
    have : 0 < T ^ 2 / 2 := by positivity
    have hee : exp ((e + kg) * T) * exp (-(e + kg) * T) = 1 := by
      rw [← exp_add]; ring_nf; simp
    calc area D e ka T ≤ D * ka * (T ^ 2 / 2) := a2
      _ = ka / kg * exp ((e + kg) * T) * (D * kg * exp (-(e + kg) * T) * (T ^ 2 / 2)) := by
          have e1 : ka / kg * exp ((e + kg) * T) * (D * kg * exp (-(e + kg) * T) * (T ^ 2 / 2)) =
              D * ka * (T ^ 2 / 2) * (exp ((e + kg) * T) * exp (-(e + kg) * T)) * (kg / kg) := by
            ring
          rw [e1, hee, div_self (ne_of_gt hkg)]; ring
      _ ≤ ka / kg * exp ((e + kg) * T) * area D e kg T := by
          apply mul_le_mul_of_nonneg_left g1; positivity

end Paper884

end Yamagishi
