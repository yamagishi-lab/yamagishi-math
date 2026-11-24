/-
論文375『第一主成分を選んでいるのは、データではなく単位である』の格上げ（一般の形）。

原稿（375_yamagishi_the_units_choose_the_principal_component/…_jp.tex）は、
相関 0.6 の正規乱数 4000 個（身長と体重）を cm・m・mm と標準化の四通りで主成分分析し、
第一主成分の向き（55.65°・89.73°・4.19°・45°）と寄与率（0.8035・1.0000・0.9898・0.7899）を示す。
「二変数の相関行列なら常に 45°」「寄与率 (1 + ρ)/2」「単位を極端にすれば寄与率はいくらでも 1 に近づく」
は言葉で述べるだけ。

ここで証明した言明（二変数の共分散行列、相関 ρ、変数 1 の単位を c 倍、u = cσ₁/σ₂ > 0）：
  (0) `scaled_cov`：単位を変えた共分散行列は σ₂² 倍の M(u) = [[u², ρu], [ρu, 1]]。
  (1) `eigen_eq`：λ₁ = (u² + 1)/2 + √(((u² − 1)/2)² + ρ²u²) について (1, t)、t = (λ₁ − u²)/(ρu) は
      M(u) の固有ベクトル。`largest`：どの (x, y) でも u²x² + 2ρuxy + y² ≤ λ₁(x² + y²)
      （λ₁ は射影した分散の最大で、第一主成分の固有値）。
  (2) 第一主成分の角 θ = arctan t（変換後の座標で測る）について、ρ > 0 なら
      `cot_two_theta`：cos 2θ/sin 2θ = (u − 1/u)/(2ρ)、
      `theta_mem`・`theta_strictAntiOn`・`theta_surj`：θ は u について狭義に減り、(0°, 90°) の上への全単射。
      `theta_one`：u = 1（二つの分散がそろう、相関行列）では θ = 45°。
  (3) 寄与率 λ₁/(u² + 1) について、|ρ| < 1 なら
      `share_ge`・`share_eq_min_iff`：寄与率 ≥ (1 + |ρ|)/2、等号 ⇔ u = 1。
      `share_lt_one_iff`：寄与率 < 1 ⇔ ρ² < 1。
      `share_surj`：[(1 + |ρ|)/2, 1) のどの値も、ある u ≥ 1 でとる（単位を極端にすれば 1 にいくらでも近い）。
足した仮定：σ₁, σ₂ > 0、c > 0。角の全単射には ρ > 0 を置いた（ρ < 0 は変数 2 の符号を変えれば同じ形で、
(90°, 180°) に移る。ここでは形式化していない）。ρ = 0 では行列が対角になり角は 0° か 90° に跳ぶ（形式化していない）。
形式化していないもの：標本の数値（標本の値と母集団の値は少しずれる）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For a two-variable covariance with correlation ρ > 0, rescaling one variable so that
u = cσ₁/σ₂ moves the first principal angle θ through cot 2θ = (u − 1/u)/(2ρ), strictly
decreasing and onto (0°, 90°); the explained share sweeps [(1 + |ρ|)/2, 1), with its minimum
only when the two variances are equal.
-/
import Mathlib

namespace Yamagishi

namespace Paper375

open Real Set

/-- 判別の平方根 √(((u² − 1)/2)² + ρ²u²)。 -/
noncomputable def disc (u ρ : ℝ) : ℝ := √(((u ^ 2 - 1) / 2) ^ 2 + ρ ^ 2 * u ^ 2)

/-- 大きいほうの固有値 λ₁。 -/
noncomputable def lam1 (u ρ : ℝ) : ℝ := (u ^ 2 + 1) / 2 + disc u ρ

/-- 第一固有ベクトル (1, t) の傾き t。 -/
noncomputable def slope (u ρ : ℝ) : ℝ := (lam1 u ρ - u ^ 2) / (ρ * u)

/-- 第一主成分の角（ラジアン）。 -/
noncomputable def theta (u ρ : ℝ) : ℝ := arctan (slope u ρ)

/-- 寄与率。 -/
noncomputable def share (u ρ : ℝ) : ℝ := lam1 u ρ / (u ^ 2 + 1)

/-- (0) 変数 1 の単位を c 倍した共分散行列は σ₂²·M(u)。 -/
theorem scaled_cov {σ₁ σ₂ ρ c : ℝ} (h₂ : 0 < σ₂) :
    (c * σ₁) ^ 2 = σ₂ ^ 2 * (c * σ₁ / σ₂) ^ 2 ∧
    ρ * (c * σ₁) * σ₂ = σ₂ ^ 2 * (ρ * (c * σ₁ / σ₂)) ∧ σ₂ ^ 2 = σ₂ ^ 2 * 1 := by
  refine ⟨?_, ?_, by ring⟩ <;> field_simp

theorem disc_nonneg (u ρ : ℝ) : 0 ≤ disc u ρ := sqrt_nonneg _

theorem disc_sq (u ρ : ℝ) : disc u ρ ^ 2 = ((u ^ 2 - 1) / 2) ^ 2 + ρ ^ 2 * u ^ 2 :=
  sq_sqrt (by positivity)

/-- 芯：(λ₁ − u²)(λ₁ − 1) = ρ²u²（特性方程式）。 -/
theorem prod_eq (u ρ : ℝ) : (lam1 u ρ - u ^ 2) * (lam1 u ρ - 1) = ρ ^ 2 * u ^ 2 := by
  unfold lam1
  linear_combination disc_sq u ρ

/-- ρu ≠ 0 なら λ₁ − u² > 0 かつ λ₁ − 1 > 0。 -/
theorem gaps_pos {u ρ : ℝ} (hu : u ≠ 0) (hρ : ρ ≠ 0) :
    0 < lam1 u ρ - u ^ 2 ∧ 0 < lam1 u ρ - 1 := by
  have hp : 0 < (lam1 u ρ - u ^ 2) * (lam1 u ρ - 1) := by
    rw [prod_eq]; positivity
  have hs : 0 ≤ (lam1 u ρ - u ^ 2) + (lam1 u ρ - 1) := by
    unfold lam1; have := disc_nonneg u ρ; linarith
  constructor
  · by_contra h
    have h' : lam1 u ρ - u ^ 2 ≤ 0 := le_of_not_gt h
    nlinarith
  · by_contra h
    have h' : lam1 u ρ - 1 ≤ 0 := le_of_not_gt h
    nlinarith

/-- (1) (1, t) は M(u) の固有ベクトルで、固有値は λ₁。 -/
theorem eigen_eq {u ρ : ℝ} (hu : u ≠ 0) (hρ : ρ ≠ 0) :
    u ^ 2 * 1 + ρ * u * slope u ρ = lam1 u ρ * 1 ∧
    ρ * u * 1 + 1 * slope u ρ = lam1 u ρ * slope u ρ := by
  have hρu : ρ * u ≠ 0 := mul_ne_zero hρ hu
  unfold slope
  constructor
  · field_simp; ring
  · have key : (lam1 u ρ - 1) * ((lam1 u ρ - u ^ 2) / (ρ * u)) = ρ * u := by
      rw [← mul_div_assoc, div_eq_iff hρu]
      linear_combination prod_eq u ρ
    linear_combination (-1 : ℝ) * key

/-- (1) λ₁ は射影した分散の最大：u²x² + 2ρuxy + y² ≤ λ₁(x² + y²)。 -/
theorem largest {u ρ : ℝ} (hu : u ≠ 0) (hρ : ρ ≠ 0) (x y : ℝ) :
    u ^ 2 * x ^ 2 + 2 * (ρ * u) * x * y + y ^ 2 ≤ lam1 u ρ * (x ^ 2 + y ^ 2) := by
  obtain ⟨ha, hc⟩ := gaps_pos hu hρ
  have hpe := prod_eq u ρ
  set a := lam1 u ρ - u ^ 2
  set c := lam1 u ρ - 1
  have key : a * (a * x ^ 2 - 2 * (ρ * u) * x * y + c * y ^ 2) = (a * x - ρ * u * y) ^ 2 := by
    linear_combination y ^ 2 * hpe
  have : 0 ≤ a * x ^ 2 - 2 * (ρ * u) * x * y + c * y ^ 2 := by
    by_contra h
    have h' := mul_neg_of_pos_of_neg ha (lt_of_not_ge h)
    rw [key] at h'
    linarith [sq_nonneg (a * x - ρ * u * y)]
  simp only [a, c] at this
  nlinarith [this]

/-- 傾き t は二次の関係 ρu t² + (u² − 1)t − ρu = 0 を満たす。 -/
theorem slope_quad {u ρ : ℝ} (hu : u ≠ 0) (hρ : ρ ≠ 0) :
    ρ * u * slope u ρ ^ 2 + (u ^ 2 - 1) * slope u ρ - ρ * u = 0 := by
  have hρu : ρ * u ≠ 0 := mul_ne_zero hρ hu
  have e : ρ * u * slope u ρ ^ 2 + (u ^ 2 - 1) * slope u ρ - ρ * u =
      ((lam1 u ρ - u ^ 2) * (lam1 u ρ - 1) - ρ ^ 2 * u ^ 2) / (ρ * u) := by
    unfold slope; field_simp; ring
  rw [e, prod_eq, sub_self, zero_div]

theorem slope_pos {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ) : 0 < slope u ρ := by
  unfold slope
  exact div_pos (gaps_pos hu.ne' hρ.ne').1 (mul_pos hρ hu)

/-- 関係式を u − 1/u = ρ(1/t − t) と書く。 -/
theorem slope_rel {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ) :
    u - 1 / u = ρ * (1 / slope u ρ - slope u ρ) := by
  have ht := slope_pos hu hρ
  have hq := slope_quad hu.ne' hρ.ne'
  field_simp
  linear_combination hq

/-- 正の t について 1/t − t は狭義に減る。 -/
theorem g_strictAnti {s t : ℝ} (hs : 0 < s) (hst : s < t) : 1 / t - t < 1 / s - s := by
  have : 1 / t < 1 / s := one_div_lt_one_div_of_lt hs hst
  linarith

/-- 傾き t は u について狭義に減る（ρ > 0）。 -/
theorem slope_strictAntiOn {ρ : ℝ} (hρ : 0 < ρ) : StrictAntiOn (fun u => slope u ρ) (Ioi 0) := by
  intro a ha b hb hab
  simp only
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have r1 := slope_rel ha' hρ
  have r2 := slope_rel hb' hρ
  have hh : a - 1 / a < b - 1 / b := by
    have : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha' hab
    linarith
  by_contra h
  have h' : slope a ρ ≤ slope b ρ := le_of_not_gt h
  rcases h'.lt_or_eq with h1 | h1
  · have := g_strictAnti (slope_pos ha' hρ) h1
    have := mul_lt_mul_of_pos_left this hρ
    linarith
  · rw [h1] at r1; linarith

/-- (2) cot 2θ = (u − 1/u)/(2ρ)。 -/
theorem cot_two_theta {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ) :
    cos (2 * theta u ρ) / sin (2 * theta u ρ) = (u - 1 / u) / (2 * ρ) := by
  have ht := slope_pos hu hρ
  set t := slope u ρ with htdef
  have hr : u - 1 / u = ρ * (1 / t - t) := slope_rel hu hρ
  unfold theta
  rw [← htdef, cos_two_mul', sin_two_mul, cos_arctan, sin_arctan]
  have hsq : 0 < √(1 + t ^ 2) := sqrt_pos.mpr (by positivity)
  have hsq2 : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := sq_sqrt (by positivity)
  rw [hr]
  field_simp

/-- (2) 0 < θ < 90°。 -/
theorem theta_mem {u ρ : ℝ} (hu : 0 < u) (hρ : 0 < ρ) : 0 < theta u ρ ∧ theta u ρ < π / 2 :=
  ⟨arctan_pos.mpr (slope_pos hu hρ), arctan_lt_pi_div_two _⟩

/-- (2) θ は u について狭義に減る。 -/
theorem theta_strictAntiOn {ρ : ℝ} (hρ : 0 < ρ) : StrictAntiOn (fun u => theta u ρ) (Ioi 0) :=
  fun _ ha _ hb hab => arctan_strictMono (slope_strictAntiOn hρ ha hb hab)

/-- (2) θ は (0, π/2) の上への写像：どの角 φ ∈ (0°, 90°) も、ある u > 0 でとる。 -/
theorem theta_surj {ρ : ℝ} (hρ : 0 < ρ) {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) :
    ∃ u, 0 < u ∧ theta u ρ = φ := by
  set t := tan φ with htdef
  have ht : 0 < t := tan_pos_of_pos_of_lt_pi_div_two hφ0 hφ1
  set s := ρ * (1 / t - t) with hsdef
  have hR0 := sqrt_nonneg (s ^ 2 + 4)
  have hR2 : √(s ^ 2 + 4) ^ 2 = s ^ 2 + 4 := sq_sqrt (by positivity)
  set u := (s + √(s ^ 2 + 4)) / 2 with hudef
  have hu : 0 < u := by
    simp only [hudef]
    by_contra h
    have h'' : 0 ≤ -s - √(s ^ 2 + 4) := by linarith [le_of_not_gt h]
    nlinarith [mul_nonneg h'' hR0, mul_nonneg h'' h'']
  refine ⟨u, hu, ?_⟩
  have hus : u - 1 / u = s := by
    have hq : u ^ 2 - s * u - 1 = 0 := by simp only [hudef]; linear_combination (1 / 4) * hR2
    field_simp
    linarith
  have r := slope_rel hu hρ
  have ht' := slope_pos hu hρ
  have heq : 1 / slope u ρ - slope u ρ = 1 / t - t := by
    have : ρ * (1 / slope u ρ - slope u ρ) = ρ * (1 / t - t) := by rw [← r, hus]
    exact mul_left_cancel₀ hρ.ne' this
  have hteq : slope u ρ = t := by
    rcases lt_trichotomy (slope u ρ) t with h | h | h
    · have := g_strictAnti ht' h; linarith
    · exact h
    · have := g_strictAnti ht h; linarith
  unfold theta
  rw [hteq, htdef, arctan_tan (by linarith [pi_pos]) hφ1]

/-- (2) u = 1（相関行列）では θ = 45°。 -/
theorem theta_one {ρ : ℝ} (hρ : 0 < ρ) : theta 1 ρ = π / 4 := by
  unfold theta slope lam1 disc
  have : √(((1 ^ 2 - 1 : ℝ) / 2) ^ 2 + ρ ^ 2 * 1 ^ 2) = ρ := by
    simp only [one_pow, sub_self, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_one, zero_add]
    exact sqrt_sq hρ.le
  rw [this]
  have : ((1 ^ 2 + 1 : ℝ) / 2 + ρ - 1 ^ 2) / (ρ * 1) = 1 := by field_simp; ring
  rw [this, arctan_one]

/-- 寄与率 = 1/2 + D/(u² + 1)。 -/
theorem share_eq (u ρ : ℝ) : share u ρ = 1 / 2 + disc u ρ / (u ^ 2 + 1) := by
  unfold share lam1
  have : 0 < u ^ 2 + 1 := by positivity
  field_simp

/-- 芯：D² − (|ρ|(u² + 1)/2)² = (1 − ρ²)(u² − 1)²/4。 -/
theorem disc_sq_sub (u ρ : ℝ) :
    disc u ρ ^ 2 - (|ρ| * (u ^ 2 + 1) / 2) ^ 2 = (1 - ρ ^ 2) * (u ^ 2 - 1) ^ 2 / 4 := by
  rw [disc_sq, show (|ρ| * (u ^ 2 + 1) / 2) ^ 2 = ρ ^ 2 * (u ^ 2 + 1) ^ 2 / 4 by
    rw [div_pow, mul_pow, sq_abs]; norm_num]
  ring

/-- (3) ρ² ≤ 1 なら 寄与率 ≥ (1 + |ρ|)/2。 -/
theorem share_ge {u ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) : (1 + |ρ|) / 2 ≤ share u ρ := by
  rw [share_eq]
  have hd : |ρ| * (u ^ 2 + 1) / 2 ≤ disc u ρ := by
    have h0 : 0 ≤ |ρ| * (u ^ 2 + 1) / 2 := by positivity
    have := disc_sq_sub u ρ
    have h1 : 0 ≤ (1 - ρ ^ 2) * (u ^ 2 - 1) ^ 2 / 4 := by
      apply div_nonneg _ (by norm_num); exact mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [disc_nonneg u ρ]
  have hp : 0 < u ^ 2 + 1 := by positivity
  rw [show (1 + |ρ|) / 2 = 1 / 2 + (|ρ| * (u ^ 2 + 1) / 2) / (u ^ 2 + 1) by field_simp]
  have := div_le_div_of_nonneg_right hd hp.le
  linarith

/-- (3) ρ² < 1、u > 0 なら、寄与率が最小値 (1 + |ρ|)/2 をとる ⇔ u = 1。 -/
theorem share_eq_min_iff {u ρ : ℝ} (hu : 0 < u) (hρ : ρ ^ 2 < 1) :
    share u ρ = (1 + |ρ|) / 2 ↔ u = 1 := by
  rw [share_eq]
  have hp : 0 < u ^ 2 + 1 := by positivity
  have e1 : 1 / 2 + disc u ρ / (u ^ 2 + 1) = (1 + |ρ|) / 2 ↔
      disc u ρ = |ρ| * (u ^ 2 + 1) / 2 := by
    constructor
    · intro h; field_simp at h; linarith
    · intro h; rw [h]; field_simp
  rw [e1]
  have hsub := disc_sq_sub u ρ
  constructor
  · intro h
    rw [h, sub_self] at hsub
    have h2 : (u ^ 2 - 1) ^ 2 = 0 := by
      have : (1 - ρ ^ 2) * (u ^ 2 - 1) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · linarith
      · exact h3
    have h3 : u ^ 2 = 1 := by nlinarith [sq_nonneg (u ^ 2 - 1)]
    nlinarith
  · intro h
    rw [h] at hsub ⊢
    simp only [one_pow, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div] at hsub
    have h0 : 0 ≤ |ρ| * (1 ^ 2 + 1) / 2 := by positivity
    have := disc_nonneg 1 ρ
    nlinarith

/-- (3) u > 0 なら、寄与率 < 1 ⇔ ρ² < 1。 -/
theorem share_lt_one_iff {u ρ : ℝ} (hu : 0 < u) : share u ρ < 1 ↔ ρ ^ 2 < 1 := by
  rw [share_eq]
  have hp : 0 < u ^ 2 + 1 := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  have e : 1 / 2 + disc u ρ / (u ^ 2 + 1) < 1 ↔ disc u ρ < (u ^ 2 + 1) / 2 := by
    rw [← lt_sub_iff_add_lt', div_lt_iff₀ hp]; constructor <;> intro h <;> linarith
  rw [e]
  unfold disc
  rw [sqrt_lt' (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- 寄与率は u について連続。 -/
theorem share_continuous (ρ : ℝ) : Continuous (fun u => share u ρ) := by
  show Continuous (fun u => ((u ^ 2 + 1) / 2 + √(((u ^ 2 - 1) / 2) ^ 2 + ρ ^ 2 * u ^ 2)) /
    (u ^ 2 + 1))
  exact Continuous.div (f := fun u => (u ^ 2 + 1) / 2 + √(((u ^ 2 - 1) / 2) ^ 2 + ρ ^ 2 * u ^ 2))
    (g := fun u => u ^ 2 + 1) (by fun_prop) (by fun_prop) (fun x => by positivity)

/-- (3) ρ² < 1 なら、[(1 + |ρ|)/2, 1) のどの値も、ある u ≥ 1 で寄与率としてとられる。 -/
theorem share_surj {ρ y : ℝ} (hρ : ρ ^ 2 < 1) (hy0 : (1 + |ρ|) / 2 ≤ y) (hy1 : y < 1) :
    ∃ u, 1 ≤ u ∧ share u ρ = y := by
  have hypos : 0 < y := by have := abs_nonneg ρ; linarith
  set U := 1 + y / (1 - y) with hU
  have h1y : 0 < 1 - y := by linarith
  have hU1 : 1 ≤ U := by have : 0 ≤ y / (1 - y) := by positivity
                         linarith
  -- share U ≥ U²/(U² + 1) > y
  have hUy : y < share U ρ := by
    rw [share_eq]
    have hp : 0 < U ^ 2 + 1 := by positivity
    have hd : (U ^ 2 - 1) / 2 ≤ disc U ρ := by
      unfold disc
      apply le_sqrt_of_sq_le
      nlinarith [sq_nonneg ρ, sq_nonneg U]
    have hU2 : y / (1 - y) < U ^ 2 := by nlinarith
    have : y < U ^ 2 / (U ^ 2 + 1) := by
      rw [lt_div_iff₀ hp]
      rw [div_lt_iff₀ h1y] at hU2
      nlinarith
    have h3 : U ^ 2 / (U ^ 2 + 1) ≤ 1 / 2 + disc U ρ / (U ^ 2 + 1) := by
      rw [show U ^ 2 / (U ^ 2 + 1) = 1 / 2 + ((U ^ 2 - 1) / 2) / (U ^ 2 + 1) by field_simp; ring]
      have := div_le_div_of_nonneg_right hd hp.le
      linarith
    linarith
  have hone : share 1 ρ = (1 + |ρ|) / 2 := by
    rw [share_eq_min_iff one_pos hρ]
  obtain ⟨u, hu, hval⟩ := intermediate_value_Icc hU1 (share_continuous ρ).continuousOn
    ⟨by rw [hone]; exact hy0, hUy.le⟩
  exact ⟨u, hu.1, hval⟩

end Paper375

end Yamagishi
