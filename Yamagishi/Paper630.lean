/-
論文630『無作為な弦が長い確率は、何を一様と置くかで 1/3 にも 1/2 にも 1/4 にもなる』の格上げ
（一般の形）。

日本語の一文：半径 1 の円で中心から弦までの距離 d の分布を、両端・半径・中点の三つの置き方で
(2/π) arcsin t・t・t² とすると、0 < t < 1 のどこでも半径の置き方が最も大きく、両端と中点の置き方では
d と弦の半長が同じ分布に従うので、どの長さ ℓ でも P(長さ > ℓ) + P(長さ > √(4 − ℓ²)) = 1 となり、
長さの中央値はともに √2、両者の大小は ℓ = √2 でただ一度入れ替わる。
English: With the distance d from the centre distributed as (2/π) arcsin t, t, t² for chords with
uniform endpoints, uniform midpoint on a radius and uniform midpoint in the disc, the radius rule is
largest for every 0 < t < 1; for the endpoint and disc rules d and the half-length are equally
distributed, so P(L > ℓ) + P(L > √(4 − ℓ²)) = 1 for every ℓ, both medians are √2, and the two rules
swap order exactly once, at ℓ = √2 (the radius rule's median is √3).

原稿（630_yamagishi_a_random_chord_is_long_with_chance_a_third_a_half_or_a_quarter/…_jp.tex）は、
境目 √3 と 1 の二つでの三つの確率（1/3・1/2・1/4 と 2/3・√3/2・3/4）と長さの平均を式と乱数で出し、
棒を投げる実験と比べている。表の 1/3 + 2/3 = 1・1/4 + 3/4 = 1 の理由（√3 と 1 が ℓ² + ℓ′² = 4 の対で
あること）には触れていない。

ここで証明した言明（距離の分布 F は [0, 1] の上の式。長さ L = 2√(1 − d²) が ℓ を越える確率を
P_F(ℓ) = F(√(1 − ℓ²/4)) と書く）：
  (1) `radius_largest`：0 < t < 1 で (2/π) arcsin t < t、t² < t。
  (2) `endpoint_half_length`・`disc_half_length`：両端と中点の置き方では、半長 √(1 − d²) が s 未満の
      確率 1 − F(√(1 − s²)) は F(s) に等しい（d と半長は同じ分布）。半径の置き方では成り立たない
      （`radius_half_length_ne`）。
      `endpoint_complement`・`disc_complement`：0 ≤ ℓ ≤ 2 で P_F(ℓ) + P_F(√(4 − ℓ²)) = 1。
      `paper_pairs`：原稿の表の値 P(√3) と P(1) は 1/3・2/3、1/2・√3/2、1/4・3/4。
  (3) `medians`：両端と中点の置き方で P(√2) = 1/2、半径の置き方で P(√3) = 1/2。
  (4) `cross_below`・`cross_above`：0 < t < √2/2 で t² < (2/π) arcsin t、√2/2 < t < 1 で
      (2/π) arcsin t < t²。`swap_once`：0 < ℓ < √2 では両端の置き方の P(ℓ) が中点の置き方より
      小さく、√2 < ℓ < 2 では大きい（大小は ℓ = √2 でだけ入れ替わる）。
  (5) `disc_from_measure`：中点を平面の円板に一様に置くと、d < t の確率は面積の比で t²
      （平面のルベーグ測度の円板の体積の尺度の性質から）。`radius_from_measure`：半径の上に一様なら t。
      `endpoint_from_measure`：両端の一方を固定し、もう一方の角を [0, π] に一様に置くと
      （d = |cos α|）、d < t の確率は (2/π) arcsin t。
足した仮定：(1)〜(4) は三つの分布の閉じた式から出る数学の言明として述べた。(5) で、それぞれの式を
一様な置き方の測度から導いた。
形式化していないもの：長さの平均 4/π・π/2・4/3、乱数と棒を投げる実験、分離子の読み。
原稿の観察 3.2「両端の置き方は短い弦を多く出す」は、√2 より短い側でだけ正しい（`swap_once`）。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper630

open Real Set MeasureTheory

/-- 両端の置き方の距離の分布 F_E(t) = (2/π) arcsin t。 -/
noncomputable def FE (t : ℝ) : ℝ := 2 / π * arcsin t

/-- 半径の置き方 F_R(t) = t。 -/
def FR (t : ℝ) : ℝ := t

/-- 中点を円板に置く置き方 F_M(t) = t²。 -/
def FM (t : ℝ) : ℝ := t ^ 2

/-- 長さが ℓ を越える確率 P_F(ℓ) = F(√(1 − ℓ²/4))。 -/
noncomputable def longProb (F : ℝ → ℝ) (ℓ : ℝ) : ℝ := F (√(1 - ℓ ^ 2 / 4))

/-- 芯：0 < u < π/2 で 1 − 2u/π < cos u。 -/
theorem cos_gt_line {u : ℝ} (h0 : 0 < u) (h1 : u < π / 2) : 1 - 2 * u / π < cos u := by
  have := mul_lt_sin (x := π / 2 - u) (by linarith) (by linarith [h0])
  rw [sin_pi_div_two_sub] at this
  have hp : 0 < π := pi_pos
  have : 2 / π * (π / 2 - u) = 1 - 2 * u / π := by field_simp
  linarith

/-- (1) 半径の置き方が最も大きい。 -/
theorem radius_largest {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : FE t < FR t ∧ FM t < FR t := by
  constructor
  · unfold FE FR
    have ha : 0 < arcsin t := arcsin_pos.mpr h0
    have hb : arcsin t < π / 2 := arcsin_lt_pi_div_two.mpr h1
    have := mul_lt_sin ha hb
    rw [sin_arcsin (by linarith) h1.le] at this
    exact this
  · unfold FM FR; nlinarith

/-- (2) 両端の置き方：F_E(√(1 − s²)) + F_E(s) = 1（0 ≤ s ≤ 1）。 -/
theorem endpoint_half_length {s : ℝ} (h0 : 0 ≤ s) :
    1 - FE (√(1 - s ^ 2)) = FE s := by
  unfold FE
  rw [← arccos_eq_arcsin h0, arccos_eq_pi_div_two_sub_arcsin]
  have := pi_pos
  field_simp
  ring

/-- (2) 中点の置き方：1 − F_M(√(1 − s²)) = F_M(s)。 -/
theorem disc_half_length {s : ℝ} (h1 : s ≤ 1) (h0 : -1 ≤ s) : 1 - FM (√(1 - s ^ 2)) = FM s := by
  unfold FM
  rw [sq_sqrt (by nlinarith)]
  ring

/-- (2) 半径の置き方では成り立たない（例：s = 1/2）。 -/
theorem radius_half_length_ne : 1 - FR (√(1 - (1 / 2 : ℝ) ^ 2)) ≠ FR (1 / 2) := by
  unfold FR
  intro h
  have : √(1 - (1 / 2 : ℝ) ^ 2) = 1 / 2 := by linarith
  have h2 : √(1 - (1 / 2 : ℝ) ^ 2) ^ 2 = (1 / 2) ^ 2 := by rw [this]
  rw [sq_sqrt (by norm_num)] at h2
  norm_num at h2

theorem sqrt_four_sub {ℓ : ℝ} (h0 : 0 ≤ ℓ) (h2 : ℓ ≤ 2) :
    √(1 - √(4 - ℓ ^ 2) ^ 2 / 4) = ℓ / 2 := by
  rw [sq_sqrt (by nlinarith)]
  rw [show 1 - (4 - ℓ ^ 2) / 4 = (ℓ / 2) ^ 2 by ring]
  exact sqrt_sq (by linarith)

theorem sqrt_one_sub {ℓ : ℝ} : √(1 - ℓ ^ 2 / 4) = √(1 - (ℓ / 2) ^ 2) := by ring_nf

/-- (2) 両端の置き方：P(ℓ) + P(√(4 − ℓ²)) = 1。 -/
theorem endpoint_complement {ℓ : ℝ} (h0 : 0 ≤ ℓ) (h2 : ℓ ≤ 2) :
    longProb FE ℓ + longProb FE (√(4 - ℓ ^ 2)) = 1 := by
  unfold longProb
  rw [sqrt_four_sub h0 h2, sqrt_one_sub]
  have := endpoint_half_length (s := ℓ / 2) (by linarith)
  linarith

/-- (2) 中点の置き方：P(ℓ) + P(√(4 − ℓ²)) = 1。 -/
theorem disc_complement {ℓ : ℝ} (h0 : 0 ≤ ℓ) (h2 : ℓ ≤ 2) :
    longProb FM ℓ + longProb FM (√(4 - ℓ ^ 2)) = 1 := by
  unfold longProb
  rw [sqrt_four_sub h0 h2, sqrt_one_sub]
  have := disc_half_length (s := ℓ / 2) (by linarith) (by linarith)
  linarith

theorem sqrt_three_sq : √3 ^ 2 = 3 := sq_sqrt (by norm_num)

theorem long_sqrt3 : √(1 - √3 ^ 2 / 4) = 1 / 2 := by
  rw [sqrt_three_sq, show (1 : ℝ) - 3 / 4 = (1 / 2) ^ 2 by norm_num]
  exact sqrt_sq (by norm_num)

theorem long_one : √(1 - (1 : ℝ) ^ 2 / 4) = √3 / 2 := by
  rw [show (1 : ℝ) - 1 ^ 2 / 4 = 3 / 4 by norm_num, sqrt_div' 3 (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]

theorem arcsin_half : arcsin (1 / 2) = π / 6 := by
  rw [← sin_pi_div_six, arcsin_sin] <;> linarith [pi_pos]

theorem arcsin_sqrt3_half : arcsin (√3 / 2) = π / 3 := by
  rw [← sin_pi_div_three, arcsin_sin] <;> linarith [pi_pos]

/-- (2) 原稿の表の値：P(√3) と P(1) の対。 -/
theorem paper_pairs :
    longProb FE √3 = 1 / 3 ∧ longProb FE 1 = 2 / 3 ∧
    longProb FR √3 = 1 / 2 ∧ longProb FR 1 = √3 / 2 ∧
    longProb FM √3 = 1 / 4 ∧ longProb FM 1 = 3 / 4 := by
  have hp := pi_pos
  unfold longProb
  rw [long_sqrt3, long_one]
  unfold FE FR FM
  rw [arcsin_half, arcsin_sqrt3_half]
  refine ⟨by field_simp; norm_num, by field_simp, rfl, rfl, by norm_num, ?_⟩
  rw [div_pow, sqrt_three_sq]; norm_num

theorem long_sqrt2 : √(1 - √2 ^ 2 / 4) = √2 / 2 := by
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), show (1 : ℝ) - 2 / 4 = 1 / 2 by norm_num]
  rw [sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), sqrt_one]
  have : 0 < √2 := sqrt_pos.mpr (by norm_num)
  field_simp
  rw [sq_sqrt (by norm_num)]

theorem arcsin_sqrt2_half : arcsin (√2 / 2) = π / 4 := by
  rw [← sin_pi_div_four, arcsin_sin] <;> linarith [pi_pos]

/-- (3) 中央値：両端と中点で √2、半径で √3。 -/
theorem medians :
    longProb FE √2 = 1 / 2 ∧ longProb FM √2 = 1 / 2 ∧ longProb FR √3 = 1 / 2 := by
  have hp := pi_pos
  unfold longProb
  rw [long_sqrt2, long_sqrt3]
  unfold FE FM FR
  rw [arcsin_sqrt2_half, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨by field_simp; norm_num, by norm_num, rfl⟩

/-- 差の形：α = arcsin t のとき F_E − F_M = (cos 2α + 4α/π − 1)/2。 -/
theorem diff_eq {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ 1) :
    FE t - FM t = (cos (2 * arcsin t) + 2 * (2 * arcsin t) / π - 1) / 2 := by
  unfold FE FM
  rw [cos_two_mul, cos_arcsin, sq_sqrt (by nlinarith)]
  ring

/-- (4) 0 < t < √2/2 で t² < (2/π) arcsin t。 -/
theorem cross_below {t : ℝ} (h0 : 0 < t) (h1 : t < √2 / 2) : FM t < FE t := by
  have hs2 : √2 / 2 < 1 := by
    have : √2 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have ha : 0 < arcsin t := arcsin_pos.mpr h0
  have hb : arcsin t < π / 4 := by
    rw [← arcsin_sqrt2_half]; exact arcsin_lt_arcsin (by linarith) h1 hs2.le
  have := cos_gt_line (u := 2 * arcsin t) (by linarith) (by linarith)
  have e := diff_eq (t := t) (by linarith) (by linarith)
  linarith

/-- (4) √2/2 < t < 1 で (2/π) arcsin t < t²。 -/
theorem cross_above {t : ℝ} (h0 : √2 / 2 < t) (h1 : t < 1) : FE t < FM t := by
  have hs0 : 0 < √2 / 2 := by have := sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num); linarith
  have ha : π / 4 < arcsin t := by
    rw [← arcsin_sqrt2_half]; exact arcsin_lt_arcsin (by linarith) h0 h1.le
  have hb : arcsin t < π / 2 := arcsin_lt_pi_div_two.mpr h1
  -- v = π − 2α は (0, π/2)
  have := cos_gt_line (u := π - 2 * arcsin t) (by linarith) (by linarith)
  rw [cos_pi_sub] at this
  have e := diff_eq (t := t) (by linarith) (by linarith)
  have hp := pi_pos
  have : 2 * (2 * arcsin t) / π = 2 - 2 * (π - 2 * arcsin t) / π := by field_simp; ring
  linarith

/-- (4) 長さで言い直す：0 < ℓ < √2 では両端の P(ℓ) < 中点の P(ℓ)、√2 < ℓ < 2 では逆。 -/
theorem swap_once {ℓ : ℝ} (h0 : 0 < ℓ) (h2 : ℓ < 2) :
    (ℓ < √2 → longProb FE ℓ < longProb FM ℓ) ∧ (√2 < ℓ → longProb FM ℓ < longProb FE ℓ) := by
  unfold longProb
  set t := √(1 - ℓ ^ 2 / 4) with ht
  have hin : 0 < 1 - ℓ ^ 2 / 4 := by nlinarith
  have ht0 : 0 < t := sqrt_pos.mpr hin
  have ht1 : t < 1 := by
    rw [ht, sqrt_lt' one_pos]; nlinarith
  have hs2 : (√2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, sq_sqrt (by norm_num)]; norm_num
  have htt : t ^ 2 = 1 - ℓ ^ 2 / 4 := sq_sqrt hin.le
  have h2sq : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := sqrt_pos.mpr (by norm_num)
  constructor
  · intro hl
    apply cross_above _ ht1
    have : ℓ ^ 2 < 2 := by nlinarith
    have : (√2 / 2) ^ 2 < t ^ 2 := by rw [hs2, htt]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 ht0.le this
  · intro hl
    apply cross_below ht0
    have : 2 < ℓ ^ 2 := by nlinarith
    have : t ^ 2 < (√2 / 2) ^ 2 := by rw [hs2, htt]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this

/-! ### 三つの式を一様な置き方から導く -/

/-- (5) 半径の上に一様：d < t の確率は t。 -/
theorem radius_from_measure {t : ℝ} (h0 : 0 ≤ t) :
    (volume (Ico (0 : ℝ) t)).toReal / (volume (Icc (0 : ℝ) 1)).toReal = FR t := by
  simp [Real.volume_Ico, Real.volume_Icc, h0, FR]

/-- (5) 円板に一様：d < t の確率は面積の比で t²。 -/
theorem disc_from_measure {t : ℝ} (h0 : 0 ≤ t) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) t)).toReal /
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal = FM t := by
  rw [Measure.addHaar_ball _ _ h0]
  rw [finrank_euclideanSpace, Fintype.card_fin]
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  field_simp
  rfl

/-- 角 α ∈ [0, π] で |cos α| < t ⇔ arccos t < α < π − arccos t（t ≤ 1）。 -/
theorem abs_cos_lt_iff {α t : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π) (ht1 : t ≤ 1) :
    |cos α| < t ↔ arccos t < α ∧ α < π - arccos t := by
  rw [abs_lt]
  have hc1 : -1 ≤ cos α := neg_one_le_cos α
  have hc2 : cos α ≤ 1 := cos_le_one α
  have hac : arccos (cos α) = α := arccos_cos hα0 hα1
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have := arccos_lt_arccos hc1 h2 ht1
      rwa [hac] at this
    · have := arccos_lt_arccos (by linarith) h1 hc2
      rw [hac, arccos_neg] at this
      exact this
  · rintro ⟨h1, h2⟩
    constructor
    · -- α < arccos(−t) ⇒ −t < cos α
      have h3 : α < arccos (-t) := by rw [arccos_neg]; exact h2
      by_contra hc; push Not at hc
      have := arccos_le_arccos hc
      rw [hac] at this; linarith
    · by_contra hc; push Not at hc
      have := arccos_le_arccos hc
      rw [hac] at this; linarith

/-- (5) 両端：もう一方の端の角の半分 α を [0, π] に一様に置くと（d = |cos α|）、
d < t の確率は (2/π) arcsin t。 -/
theorem endpoint_from_measure {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (volume {α ∈ Icc 0 π | |cos α| < t}).toReal / (volume (Icc 0 π)).toReal = FE t := by
  have hset : {α ∈ Icc 0 π | |cos α| < t} = Ioo (arccos t) (π - arccos t) := by
    ext α
    simp only [mem_ofPred_eq, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      exact (abs_cos_lt_iff ha hb h1).mp h
    · rintro ⟨ha, hb⟩
      have hac := arccos_nonneg t
      have hα0 : 0 ≤ α := by linarith
      have hα1 : α ≤ π := by linarith
      exact ⟨⟨hα0, hα1⟩, (abs_cos_lt_iff hα0 hα1 h1).mpr ⟨ha, hb⟩⟩
  rw [hset, Real.volume_Ioo, Real.volume_Icc]
  have hp := pi_pos
  have hle : arccos t ≤ π / 2 := arccos_le_pi_div_two.mpr h0
  rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  unfold FE
  rw [arccos_eq_pi_div_two_sub_arcsin]
  field_simp
  ring

end Paper630

end Yamagishi
