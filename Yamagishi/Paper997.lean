/-
論文997『明るさに比例して風で質量を失う星は、燃料ごと失っても寿命が延び、延び方は星の重さによらない』の
格上げ（一般の形）。

日本語の一文：明るさを質量の p 乗とし、風も燃料の消費も明るさに比例するとき、寿命の倍率は初めの質量にも
明るさの係数にもよらず、燃料ごと持ち去る風では p > 1 のときだけ 1 を超え、外側だけを持ち去る風では
p > 0 のときだけ 1 を超え、どの p でも外側だけのほうが長い。
English: With luminosity L = kM^p, wind dM/dt = −βL and burning at rate L/c (fuel f·M₀ at
the start, wind strength ε = βfc), the lifetime divided by the windless lifetime is
(∫_{y}^{1} s^(−p) ds)/ε with y = e^(−ε) if the wind takes fuel along and y = 1 − ε if it takes
only the envelope; it does not depend on M₀ or k; it exceeds 1 exactly when p > 1 (fuel along) or
p > 0 (envelope only), and the envelope-only lifetime is always the longer one.

原稿（997_yamagishi_a_star_losing_mass_in_a_wind_lives_longer_whatever_its_mass/…_jp.tex）は、
p = 3.5、ε = 0.1・0.3・0.5・0.9、質量 1・5・20 で寿命を刻んで出し、閉じた形
(e^(ε(p−1)) − 1)/(ε(p−1)) と ((1 − ε)^(−(p−1)) − 1)/(ε(p−1)) と比べている。閉じた形の導きは第 1 節に
p の記号で書いてあるが、倍率が 1 を超える条件と二つの大小は p = 3.5 の数だけ。

ここで証明した言明（k, β, c, f, M₀ > 0、p は実数）：
  (1) `fuel_end_mass`：燃料ごと持ち去る系 dM/dt = −βkM^p、dF/dt = −kM^p/c − βkM^p·F/M の解では
      F/M − ln M/(cβ) が一定。よって燃料が尽きる時刻の質量は M₀e^(−ε)（ε = βfc）。
      `outer_end_mass`：外側だけの系 dF/dt = −kM^p/c では F − M/(cβ) が一定で、尽きる質量は M₀(1 − ε)。
  (2) `time_integral`：dM/dt = −βkM^p の解では βk·T = ∫_{M(T)}^{M(0)} x^(−p) dx。
      `lifetime_ratio`：寿命 ÷ 風なしの寿命 fcM₀/(kM₀^p) = life(y) = (∫_y^1 s^(−p) ds)/ε で、
      M₀ にも k にもよらない（y は燃料ごとで e^(−ε)、外側だけで 1 − ε）。
  (3) `fuel_gt_one_iff`・`fuel_eq_one_iff`・`fuel_lt_one_iff`：燃料ごとの倍率 life(e^(−ε)) は
      p > 1 ⇔ 1 より大、p = 1 ⇔ 1、p < 1 ⇔ 1 より小（被積分の s^(−p) と s^(−1) を比べる）。
  (4) `outer_gt_one_iff`・`outer_eq_one_iff`・`outer_lt_one_iff`：0 < ε < 1 で、外側だけの倍率
      life(1 − ε) は p > 0 ⇔ 1 より大、p = 0 ⇔ 1、p < 0 ⇔ 1 より小（s^(−p) と 1 を比べる）。
  (5) `outer_gt_fuel`：どの p でも、外側だけの倍率 > 燃料ごとの倍率（1 − ε < e^(−ε) で区間が広い）。
  (6) `fuel_closed`・`outer_closed`：p ≠ 1 で原稿の閉じた形に等しい。
足した仮定：明るさ L = kM^p、風と燃料の消費が明るさに比例すること、二つの持ち去り方の燃料の式を、
原稿のとおり定義（微分方程式の解についての仮定）として置いた。燃料が尽きる時刻 T までは解が在り、
質量は正であることを仮定に置いた。
形式化していないもの：原稿の数表の値（e^(1.25) などの数値）、刻んだ寿命との一致、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper997

open Real Set intervalIntegral MeasureTheory

/-! ### 原始関数と積分 -/

/-- s^(−p) の原始関数：p = 1 なら ln m、それ以外は m^(1−p)/(1 − p)。 -/
noncomputable def G (p m : ℝ) : ℝ := if p = 1 then log m else m ^ (1 - p) / (1 - p)

theorem hasDerivAt_G (p : ℝ) {m : ℝ} (hm : 0 < m) : HasDerivAt (G p) (m ^ (-p)) m := by
  by_cases hp : p = 1
  · have e : G p = log := by funext x; simp [G, hp]
    rw [e, hp, rpow_neg_one]
    exact hasDerivAt_log (ne_of_gt hm)
  · have e : G p = fun x => x ^ (1 - p) / (1 - p) := by funext x; simp [G, hp]
    have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
    rw [e]
    have := (hasDerivAt_rpow_const (x := m) (p := 1 - p) (Or.inl (ne_of_gt hm))).div_const (1 - p)
    convert this using 1
    rw [show 1 - p - 1 = -p by ring]
    field_simp

theorem continuousOn_rpow_neg (p : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun x : ℝ => x ^ (-p)) (uIcc a b) := by
  intro x hx
  have : 0 < x := by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hx; linarith [hx.1]
    · rw [uIcc_of_ge h] at hx; linarith [hx.1]
  exact (continuousAt_rpow_const x (-p) (Or.inl (ne_of_gt this))).continuousWithinAt

/-- ∫_a^b x^(−p) dx = G(b) − G(a)（a, b > 0）。 -/
theorem integral_eq_G (p : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, x ^ (-p) = G p b - G p a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    have : 0 < x := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hx; linarith [hx.1]
      · rw [uIcc_of_ge h] at hx; linarith [hx.1]
    exact hasDerivAt_G p this
  · exact (continuousOn_rpow_neg p ha hb).intervalIntegrable

/-- 尺度の変え方：G(M₀) − G(M₀y) = M₀^(1−p)·(G(1) − G(y))。 -/
theorem G_scale (p : ℝ) {M₀ y : ℝ} (hM : 0 < M₀) (hy : 0 < y) :
    G p M₀ - G p (M₀ * y) = M₀ ^ (1 - p) * (G p 1 - G p y) := by
  unfold G
  by_cases hp : p = 1
  · simp only [hp, ite_true, sub_self, rpow_zero, one_mul, log_one, zero_sub]
    rw [log_mul (ne_of_gt hM) (ne_of_gt hy)]; ring
  · simp only [hp, ite_false, one_rpow]
    rw [mul_rpow hM.le hy.le]
    ring

/-! ### 寿命の倍率 -/

/-- 寿命の倍率 life(y) = (∫_y^1 s^(−p) ds)/ε。 -/
noncomputable def life (p ε y : ℝ) : ℝ := (∫ s in y..1, s ^ (-p)) / ε

/-- 定数で止めておく小さな道具：導関数が 0 なら [0, T] で一定。 -/
theorem const_of_deriv_zero {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ s ∈ Icc 0 T, HasDerivAt g 0 s) : g T = g 0 := by
  have hcont : ContinuousOn g (Icc 0 T) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) T ⟨hT, le_rfl⟩

/-- (2) dM/dt = −βkM^p の解では βk·T = ∫_{M(T)}^{M(0)} x^(−p) dx。 -/
theorem time_integral {p k β T : ℝ} (hT : 0 ≤ T) (M : ℝ → ℝ)
    (hM : ∀ s ∈ Icc 0 T, HasDerivAt M (-(β * (k * M s ^ p))) s)
    (hpos : ∀ s ∈ Icc 0 T, 0 < M s) :
    β * k * T = ∫ x in M T..M 0, x ^ (-p) := by
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt (fun u => G p (M u) + β * k * u) 0 s := by
    intro s hs
    have h1 := (hasDerivAt_G p (hpos s hs)).comp s (hM s hs)
    have h2 := ((hasDerivAt_id s).const_mul (β * k))
    have := h1.add h2
    have h' : HasDerivAt (fun u => G p (M u) + β * k * u)
        (M s ^ (-p) * -(β * (k * M s ^ p)) + β * k * 1) s := this
    convert h' using 1
    have hm := hpos s hs
    rw [rpow_neg hm.le]
    have : M s ^ p ≠ 0 := ne_of_gt (rpow_pos_of_pos hm p)
    field_simp
    ring
  have := const_of_deriv_zero hT hd
  simp only [mul_zero, add_zero] at this
  rw [integral_eq_G p (hpos T ⟨hT, le_rfl⟩) (hpos 0 ⟨le_rfl, hT⟩)]
  linarith

/-- (1) 燃料ごと持ち去る系：燃料が尽きる時刻の質量は M₀e^(−βfc)。 -/
theorem fuel_end_mass {p k β c f T : ℝ} (hβ : 0 < β) (hc : 0 < c) (hT : 0 ≤ T)
    (M F : ℝ → ℝ) (hM : ∀ s ∈ Icc 0 T, HasDerivAt M (-(β * (k * M s ^ p))) s)
    (hF : ∀ s ∈ Icc 0 T, HasDerivAt F (-(k * M s ^ p / c) - β * (k * M s ^ p) * (F s / M s)) s)
    (hpos : ∀ s ∈ Icc 0 T, 0 < M s) (hF0 : F 0 = f * M 0) (hFT : F T = 0) :
    M T = M 0 * exp (-(β * f * c)) := by
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt (fun u => F u / M u - log (M u) / (c * β)) 0 s := by
    intro s hs
    have hm := hpos s hs
    have h1 := (hF s hs).div (hM s hs) (ne_of_gt hm)
    have h2 := ((hM s hs).log (ne_of_gt hm)).div_const (c * β)
    have := h1.sub h2
    convert this using 1
    field_simp
    ring
  have := const_of_deriv_zero hT hd
  have hm0 := hpos 0 ⟨le_rfl, hT⟩
  have hmT := hpos T ⟨hT, le_rfl⟩
  rw [hFT, hF0, zero_div, zero_sub, mul_div_cancel_right₀ _ (ne_of_gt hm0)] at this
  have hl : log (M T) = log (M 0) - β * f * c := by
    field_simp at this
    linarith
  rw [← exp_log hmT, hl, exp_sub, exp_log hm0, exp_neg, div_eq_mul_inv]

/-- (1) 外側だけを持ち去る系：燃料が尽きる時刻の質量は M₀(1 − βfc)。 -/
theorem outer_end_mass {p k β c f T : ℝ} (hβ : 0 < β) (hc : 0 < c) (hT : 0 ≤ T)
    (M F : ℝ → ℝ) (hM : ∀ s ∈ Icc 0 T, HasDerivAt M (-(β * (k * M s ^ p))) s)
    (hF : ∀ s ∈ Icc 0 T, HasDerivAt F (-(k * M s ^ p / c)) s)
    (hF0 : F 0 = f * M 0) (hFT : F T = 0) :
    M T = M 0 * (1 - β * f * c) := by
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt (fun u => F u - M u / (c * β)) 0 s := by
    intro s hs
    have := (hF s hs).sub ((hM s hs).div_const (c * β))
    convert this using 1
    field_simp
    ring
  have := const_of_deriv_zero hT hd
  rw [hFT, hF0] at this
  field_simp at this
  linarith

/-- (2) 寿命 ÷ 風なしの寿命 = life(y)：初めの質量 M₀ と係数 k は消える。 -/
theorem lifetime_ratio {p k β c f T y : ℝ} (hβ : 0 < β) (hc : 0 < c) (hf : 0 < f)
    (hT : 0 ≤ T) (hy : 0 < y) (M : ℝ → ℝ)
    (hM : ∀ s ∈ Icc 0 T, HasDerivAt M (-(β * (k * M s ^ p))) s)
    (hpos : ∀ s ∈ Icc 0 T, 0 < M s) (hend : M T = M 0 * y) :
    T / (f * c * M 0 / (k * M 0 ^ p)) = life p (β * f * c) y := by
  have hm0 := hpos 0 ⟨le_rfl, hT⟩
  have hti := time_integral hT M hM hpos
  rw [hend, integral_eq_G p (by positivity) hm0, G_scale p hm0 hy, ← integral_eq_G p hy one_pos]
    at hti
  unfold life
  have hMp : M 0 ^ p ≠ 0 := ne_of_gt (rpow_pos_of_pos hm0 p)
  have hM1 : M 0 ^ (1 - p) = M 0 / M 0 ^ p := by
    rw [rpow_sub hm0, rpow_one]
  rw [hM1] at hti
  field_simp
  field_simp at hti
  linarith

/-! ### 倍率と 1 の大小 -/

/-- ∫_y^1 s^(−1) ds = −ln y = ε（y = e^(−ε)）。 -/
theorem integral_inv_exp {ε : ℝ} : ∫ s in exp (-ε)..1, s ^ (-(1 : ℝ)) = ε := by
  rw [integral_eq_G 1 (exp_pos _) one_pos]
  simp [G]

/-- ∫_y^1 s^0 ds = 1 − y。 -/
theorem integral_one {y : ℝ} (hy : 0 < y) : ∫ s in y..1, s ^ (-(0 : ℝ)) = 1 - y := by
  rw [integral_eq_G 0 hy one_pos]
  simp [G]

/-- 二つの被積分関数を (y, 1) で比べて、積分の大小を出す道具。 -/
theorem integral_lt_of_lt {f g : ℝ → ℝ} {y : ℝ} (hy1 : y < 1)
    (hf : ContinuousOn f (Icc y 1)) (hg : ContinuousOn g (Icc y 1))
    (hle : ∀ s ∈ Ioc y 1, f s ≤ g s) (hlt : f y < g y) :
    ∫ s in y..1, f s < ∫ s in y..1, g s :=
  integral_lt_integral_of_continuousOn_of_le_of_exists_lt hy1 hf hg hle ⟨y, ⟨le_rfl, hy1.le⟩, hlt⟩

theorem cont_rpow (p : ℝ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ContinuousOn (fun s : ℝ => s ^ (-p)) (Icc y 1) := by
  have := continuousOn_rpow_neg p hy one_pos
  rwa [uIcc_of_le hy1] at this

/-- 0 < s < 1 で s^(−p) と s^(−q) の大小は p と q の大小と同じ。 -/
theorem rpow_neg_lt {s p q : ℝ} (hs : 0 < s) (hs1 : s < 1) (hpq : p < q) :
    s ^ (-p) < s ^ (-q) :=
  rpow_lt_rpow_of_exponent_gt hs hs1 (by linarith)

theorem fuel_cmp {p ε : ℝ} (hε : 0 < ε) :
    (1 < p → 1 < life p ε (exp (-ε))) ∧ (p = 1 → life p ε (exp (-ε)) = 1) ∧
    (p < 1 → life p ε (exp (-ε)) < 1) := by
  have hy := exp_pos (-ε)
  have hy1 : exp (-ε) < 1 := by rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  unfold life
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · rw [one_lt_div hε]
    have := integral_lt_of_lt hy1 (cont_rpow 1 hy hy1.le) (cont_rpow p hy hy1.le)
      (fun s hs => (rpow_le_rpow_of_exponent_ge (by linarith [hs.1]) hs.2 (by linarith)))
      (rpow_neg_lt hy hy1 hp)
    rwa [integral_inv_exp] at this
  · rw [hp, integral_inv_exp, div_self (ne_of_gt hε)]
  · rw [div_lt_one hε]
    have := integral_lt_of_lt hy1 (cont_rpow p hy hy1.le) (cont_rpow 1 hy hy1.le)
      (fun s hs => (rpow_le_rpow_of_exponent_ge (by linarith [hs.1]) hs.2 (by linarith)))
      (rpow_neg_lt hy hy1 hp)
    rwa [integral_inv_exp] at this

/-- (3) 燃料ごとの倍率は p > 1 のときだけ 1 を超える。 -/
theorem fuel_gt_one_iff {p ε : ℝ} (hε : 0 < ε) : 1 < life p ε (exp (-ε)) ↔ 1 < p := by
  obtain ⟨h1, h2, h3⟩ := fuel_cmp (p := p) hε
  constructor
  · intro h
    rcases lt_trichotomy p 1 with hp | hp | hp
    · linarith [h3 hp]
    · linarith [h2 hp]
    · exact hp
  · exact h1

theorem fuel_eq_one_iff {p ε : ℝ} (hε : 0 < ε) : life p ε (exp (-ε)) = 1 ↔ p = 1 := by
  obtain ⟨h1, h2, h3⟩ := fuel_cmp (p := p) hε
  constructor
  · intro h
    rcases lt_trichotomy p 1 with hp | hp | hp
    · linarith [h3 hp]
    · exact hp
    · linarith [h1 hp]
  · exact h2

theorem fuel_lt_one_iff {p ε : ℝ} (hε : 0 < ε) : life p ε (exp (-ε)) < 1 ↔ p < 1 := by
  obtain ⟨h1, h2, h3⟩ := fuel_cmp (p := p) hε
  constructor
  · intro h
    rcases lt_trichotomy p 1 with hp | hp | hp
    · exact hp
    · linarith [h2 hp]
    · linarith [h1 hp]
  · exact h3

theorem outer_cmp {p ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (0 < p → 1 < life p ε (1 - ε)) ∧ (p = 0 → life p ε (1 - ε) = 1) ∧
    (p < 0 → life p ε (1 - ε) < 1) := by
  have hy : 0 < 1 - ε := by linarith
  have hy1 : 1 - ε < 1 := by linarith
  have hI := integral_one hy
  rw [show 1 - (1 - ε) = ε by ring] at hI
  unfold life
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · rw [one_lt_div hε]
    have := integral_lt_of_lt hy1 (cont_rpow 0 hy hy1.le) (cont_rpow p hy hy1.le)
      (fun s hs => (rpow_le_rpow_of_exponent_ge (by linarith [hs.1]) hs.2 (by linarith)))
      (rpow_neg_lt hy hy1 hp)
    rwa [hI] at this
  · rw [hp, hI, div_self (ne_of_gt hε)]
  · rw [div_lt_one hε]
    have := integral_lt_of_lt hy1 (cont_rpow p hy hy1.le) (cont_rpow 0 hy hy1.le)
      (fun s hs => (rpow_le_rpow_of_exponent_ge (by linarith [hs.1]) hs.2 (by linarith)))
      (rpow_neg_lt hy hy1 hp)
    rwa [hI] at this

/-- (4) 外側だけの倍率は p > 0 のときだけ 1 を超える（0 < ε < 1）。 -/
theorem outer_gt_one_iff {p ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 < life p ε (1 - ε) ↔ 0 < p := by
  obtain ⟨h1, h2, h3⟩ := outer_cmp (p := p) hε hε1
  constructor
  · intro h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · linarith [h3 hp]
    · linarith [h2 hp]
    · exact hp
  · exact h1

theorem outer_eq_one_iff {p ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    life p ε (1 - ε) = 1 ↔ p = 0 := by
  obtain ⟨h1, h2, h3⟩ := outer_cmp (p := p) hε hε1
  constructor
  · intro h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · linarith [h3 hp]
    · exact hp
    · linarith [h1 hp]
  · exact h2

theorem outer_lt_one_iff {p ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    life p ε (1 - ε) < 1 ↔ p < 0 := by
  obtain ⟨h1, h2, h3⟩ := outer_cmp (p := p) hε hε1
  constructor
  · intro h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · exact hp
    · linarith [h2 hp]
    · linarith [h1 hp]
  · exact h3

/-- (5) どの p でも、外側だけの倍率は燃料ごとの倍率より大きい。 -/
theorem outer_gt_fuel {p ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    life p ε (exp (-ε)) < life p ε (1 - ε) := by
  have hy : 0 < 1 - ε := by linarith
  have hlt : 1 - ε < exp (-ε) := by linarith [add_one_lt_exp (show -ε ≠ 0 by linarith)]
  unfold life
  apply div_lt_div_of_pos_right _ hε
  rw [integral_eq_G p (exp_pos _) one_pos, integral_eq_G p hy one_pos]
  -- G は (0, ∞) で狭義に増える
  have hmono : StrictMonoOn (G p) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun x hx => (hasDerivAt_G p hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(hasDerivAt_G p hx).deriv]
      exact rpow_pos_of_pos hx _
  have h2 : G p (1 - ε) < G p (exp (-ε)) :=
    hmono (show (1 - ε) ∈ Ioi (0 : ℝ) from hy) (show exp (-ε) ∈ Ioi (0 : ℝ) from exp_pos _) hlt
  linarith

/-- (6) p ≠ 1 での燃料ごとの閉じた形 (e^(ε(p−1)) − 1)/(ε(p−1))。 -/
theorem fuel_closed {p ε : ℝ} (hp : p ≠ 1) (hε : ε ≠ 0) :
    life p ε (exp (-ε)) = (exp (ε * (p - 1)) - 1) / (ε * (p - 1)) := by
  unfold life
  rw [integral_eq_G p (exp_pos _) one_pos]
  have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  simp only [G, hp, ite_false, one_rpow]
  rw [← exp_mul, show -ε * (1 - p) = ε * (p - 1) by ring]
  field_simp
  ring

/-- (6) p ≠ 1 での外側だけの閉じた形 ((1 − ε)^(−(p−1)) − 1)/(ε(p−1))。 -/
theorem outer_closed {p ε : ℝ} (hp : p ≠ 1) (hε : ε ≠ 0) (hε1 : ε < 1) :
    life p ε (1 - ε) = ((1 - ε) ^ (-(p - 1)) - 1) / (ε * (p - 1)) := by
  unfold life
  rw [integral_eq_G p (by linarith) one_pos]
  have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  simp only [G, hp, ite_false, one_rpow]
  rw [show -(p - 1) = 1 - p by ring]
  field_simp
  ring

end Paper997

end Yamagishi
