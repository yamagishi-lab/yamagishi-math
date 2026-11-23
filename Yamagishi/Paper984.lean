/-
論文984『近交は劣性の変異が固定する確率を最も押し上げ、近交係数 1 では優性の度合いの差が消える』の
格上げ（一般の形）。

日本語の一文：近交係数 F を入れたライト＝フィッシャー模型で、優性の度合いが 0 ≤ h ≤ 1 なら、有利な変異が
固定する確率は、どの集団の大きさでも F について減らず、F = 1 では h が消える。h > 1 では一世代の段で
向きが逆になりうる。
English: In the Wright–Fisher model with genotype frequencies p² + Fpq, 2pq(1 − F), q² + Fpq and
binomial resampling of M copies, for 0 ≤ h ≤ 1 and s > 0 the fixation probability from any number of
copies is nondecreasing in F, for every M; this rests on dp′/dF = s·pq((1 − h)q + hp(1 + s))/w̄², on
p′ increasing in p, and on the monotonicity of binomial expectations; at F = 1 the chain does not
depend on h; for h = 2 the one-generation map can decrease in F although s > 0.

原稿（984_yamagishi_inbreeding_lifts_recessive_fixation_most_and_full_inbreeding_erases_dominance/
…_jp.tex）は、N = 50・s = 0.05 と N = 200・s = 0.01 の二つの設定で、F 六つ・h 三つの遷移行列を厳密に解き、
固定する確率が F とともに増えること、F = 1 で三つの h の値が半数体の値と一致することを示す。

ここで証明した言明（0 < p < 1、q = 1 − p、0 ≤ F ≤ 1）：
  (1) `hasDerivAt_F`：p′ の F についての微分は s·pq((1 − h)q + hp(1 + s))/w̄²。
  (2) `strictMonoOn_F`：0 ≤ h ≤ 1、s > 0 なら p′ は F について [0, 1] で狭義に増える。
      `strictAntiOn_F`：0 ≤ h ≤ 1、−1 < s < 0 なら狭義に減る。
  (3) `full_inbreeding`：F = 1 では p′ = p(1 + s)/(1 + ps)（h によらない。写しの数 2N の半数体と同じ式なので、
      二項分布で引き直す遷移行列も半数体と同じになる）。
  (4) `overdominance_counterexample`：h = 2、s = 1/20、p = 1/10 では p′ は F について [0, 1] で狭義に減る
      （条件 h ≤ 1 は一世代の段では外せない）。
  (5) `p'_strictMonoOn_p`：0 ≤ h ≤ 1、s > −1、0 ≤ F ≤ 1 なら p′ は p について [0, 1] で狭義に増える。
  (6) `binE_eq_sum`・`binE_mono_x`：二項分布 Bin(n, x) での期待値（一回目の引きで分けて定義し、
      Σ C(n, j) x^j (1 − x)^(n−j) g(j) と同じと示した）は、増える g について x とともに増える。
  (7) `fixBy_mono_F`：写し M 個（M ≥ 1）の模型で、s > 0、0 ≤ h ≤ 1、F₁ ≤ F₂ なら、どの写しの数 i から
      でも、n 世代のうちに固定している確率は F₂ のほうが大きいか等しい。
      `fixProb_mono_F`：その極限（固定する確率、`fixBy_tendsto` で収束する）も同じ。一つの写しからは i = 1。
  (8) `fixProb_full`：F = 1 では固定する確率は h によらない（半数体の式 p(1 + s)/(1 + ps) の遷移）。
足した仮定：なし（模型の式は原稿のとおり定義に置いた。写しの数は M のままで、近交で有効な集団の大きさが
変わることは入れていない。原稿と同じ）。
形式化していないもの：押し上げの倍率が劣性で最も大きいこと（証明の筋が立っていない）、h > 1 で固定する
確率そのものが下がる例（下読みの AI の計算では N = 20 で 0.1141 から 0.0953）、数表の値、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper984

open Set

/-- 選択のあとの A の割合の分子 A(F) = AA(1 + s) + Aa(1 + hs)/2。 -/
def num (p h s F : ℝ) : ℝ :=
  (p ^ 2 + F * p * (1 - p)) * (1 + s) + p * (1 - p) * (1 - F) * (1 + h * s)

/-- 平均の適応度 w̄ = AA(1 + s) + Aa(1 + hs) + aa。 -/
def wbar (p h s F : ℝ) : ℝ :=
  (p ^ 2 + F * p * (1 - p)) * (1 + s) + 2 * p * (1 - p) * (1 - F) * (1 + h * s)
    + ((1 - p) ^ 2 + F * p * (1 - p))

/-- 選択のあとの割合 p′ = A/w̄。 -/
noncomputable def p' (p h s F : ℝ) : ℝ := num p h s F / wbar p h s F

theorem wbar_pos {p h s F : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : -1 < s) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : 0 < wbar p h s F := by
  unfold wbar
  have hq : 0 < 1 - p := by linarith
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + h * s := by
    rcases le_or_gt 0 s with hs0 | hs0
    · nlinarith
    · nlinarith [mul_le_mul_of_nonpos_right hh1 hs0.le]
  have hpq : 0 < p * (1 - p) := mul_pos hp0 hq
  have a1 : 0 < p ^ 2 + F * p * (1 - p) := by nlinarith
  have a2 : 0 ≤ 2 * p * (1 - p) * (1 - F) * (1 + h * s) := by
    have : 0 ≤ 1 - F := by linarith
    positivity
  have a3 : 0 < (1 - p) ^ 2 + F * p * (1 - p) := by nlinarith
  nlinarith

/-- 微分の分子の恒等式。 -/
theorem deriv_numerator (p h s F : ℝ) :
    s * p * (1 - p) * (1 - h) * wbar p h s F - num p h s F * (s * p * (1 - p) * (1 - 2 * h)) =
      s * p * (1 - p) * ((1 - h) * (1 - p) + h * p * (1 + s)) := by
  unfold wbar num; ring

/-- (1) dp′/dF = s·pq((1 − h)q + hp(1 + s))/w̄²。 -/
theorem hasDerivAt_F (p h s F : ℝ) (hw : wbar p h s F ≠ 0) :
    HasDerivAt (fun F => p' p h s F)
      (s * p * (1 - p) * ((1 - h) * (1 - p) + h * p * (1 + s)) / wbar p h s F ^ 2) F := by
  have hA : HasDerivAt (fun F => num p h s F) (s * p * (1 - p) * (1 - h)) F := by
    unfold num
    have := ((((hasDerivAt_id' F).mul_const (p * (1 - p))).const_add (p ^ 2)).mul_const (1 + s)).add
      ((((hasDerivAt_id' F).const_sub 1).const_mul (p * (1 - p))).mul_const (1 + h * s))
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun x => by simp only [Pi.add_apply]; ring)
  have hW : HasDerivAt (fun F => wbar p h s F) (s * p * (1 - p) * (1 - 2 * h)) F := by
    unfold wbar
    have := (((((hasDerivAt_id' F).mul_const (p * (1 - p))).const_add (p ^ 2)).mul_const
      (1 + s)).add ((((hasDerivAt_id' F).const_sub 1).const_mul (2 * p * (1 - p))).mul_const
      (1 + h * s))).add (((hasDerivAt_id' F).mul_const (p * (1 - p))).const_add ((1 - p) ^ 2))
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun x => by simp only [Pi.add_apply]; ring)
  have := hA.div hW hw
  unfold p'
  refine this.congr_deriv ?_
  rw [deriv_numerator]

/-- 0 ≤ h ≤ 1、s > −1 なら (1 − h)q + hp(1 + s) > 0。 -/
theorem bracket_pos {p h s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : -1 < s) : 0 < (1 - h) * (1 - p) + h * p * (1 + s) := by
  have h1 : 0 < 1 + s := by linarith
  rcases eq_or_lt_of_le hh0 with he | hlt
  · rw [← he]; linarith
  · have : 0 < h * p * (1 + s) := by positivity
    have : 0 ≤ (1 - h) * (1 - p) := mul_nonneg (by linarith) (by linarith)
    linarith

/-- (2) 0 ≤ h ≤ 1、s > 0 なら p′ は F について [0, 1] で狭義に増える。 -/
theorem strictMonoOn_F {p h s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : 0 < s) : StrictMonoOn (fun F => p' p h s F) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro F hF
    exact (hasDerivAt_F p h s F (wbar_pos hp0 hp1 hh0 hh1 (by linarith) hF.1 hF.2).ne')
      |>.continuousAt.continuousWithinAt
  · intro F hF
    rw [interior_Icc] at hF
    have hw := wbar_pos hp0 hp1 hh0 hh1 (by linarith) hF.1.le hF.2.le
    rw [(hasDerivAt_F p h s F hw.ne').deriv]
    have := bracket_pos hp0 hp1 hh0 hh1 (by linarith : -1 < s)
    have : 0 < 1 - p := by linarith
    positivity

/-- (2) 0 ≤ h ≤ 1、−1 < s < 0 なら p′ は F について [0, 1] で狭義に減る。 -/
theorem strictAntiOn_F {p h s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs1 : -1 < s) (hs : s < 0) : StrictAntiOn (fun F => p' p h s F) (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · intro F hF
    exact (hasDerivAt_F p h s F (wbar_pos hp0 hp1 hh0 hh1 hs1 hF.1 hF.2).ne')
      |>.continuousAt.continuousWithinAt
  · intro F hF
    rw [interior_Icc] at hF
    have hw := wbar_pos hp0 hp1 hh0 hh1 hs1 hF.1.le hF.2.le
    rw [(hasDerivAt_F p h s F hw.ne').deriv]
    have hb := bracket_pos hp0 hp1 hh0 hh1 hs1
    have hq : 0 < 1 - p := by linarith
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < p * (1 - p) * ((1 - h) * (1 - p) + h * p * (1 + s)) := by positivity
    nlinarith

/-- (3) F = 1 では p′ = p(1 + s)/(1 + ps)（h によらない）。 -/
theorem full_inbreeding (p h s : ℝ) : p' p h s 1 = p * (1 + s) / (1 + p * s) := by
  unfold p' num wbar
  congr 1 <;> ring

/-- (4) h = 2、s = 1/20、p = 1/10 では p′ は F について [0, 1] で狭義に減る。 -/
theorem overdominance_counterexample :
    StrictAntiOn (fun F => p' (1 / 10) 2 (1 / 20) F) (Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
  · intro F hF
    have hw : wbar (1 / 10) 2 (1 / 20) F ≠ 0 := by
      unfold wbar; have := hF.1; have := hF.2; nlinarith
    exact (hasDerivAt_F _ _ _ F hw).continuousAt.continuousWithinAt
  · intro F hF
    rw [interior_Icc] at hF
    have hw : 0 < wbar (1 / 10) 2 (1 / 20) F := by
      unfold wbar; have := hF.1; have := hF.2; nlinarith
    rw [(hasDerivAt_F _ _ _ F hw.ne').deriv]
    apply div_neg_of_neg_of_pos _ (by positivity)
    norm_num

/-! ### p′ は p について増える（0 ≤ h ≤ 1、s > −1） -/

/-- N(p) = 1 + hs + s(1 − h)(F + (1 − F)p)。分子 = p·N。 -/
def Nf (p h s F : ℝ) : ℝ := 1 + h * s + s * (1 - h) * (F + (1 - F) * p)

/-- D(p) = 1 + hs(1 − F)p。w̄ − 分子 = (1 − p)·D。 -/
def Df (p h s F : ℝ) : ℝ := 1 + h * s * (1 - F) * p

theorem num_eq_pN (p h s F : ℝ) : num p h s F = p * Nf p h s F := by unfold num Nf; ring

theorem wbar_eq (p h s F : ℝ) : wbar p h s F = p * Nf p h s F + (1 - p) * Df p h s F := by
  unfold wbar Nf Df; ring

section params

variable {h s F : ℝ}

theorem Nf_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : 0 < Nf p h s F := by
  have hw0 : 0 ≤ F + (1 - F) * p := by nlinarith
  have hw1 : F + (1 - F) * p ≤ 1 := by nlinarith
  have e : Nf p h s F = (1 + h * s) * (1 - (F + (1 - F) * p)) + (1 + s) * (F + (1 - F) * p) := by
    unfold Nf; ring
  have h1 : 0 < 1 + h * s := by
    rcases le_or_gt 0 s with hs0 | hs0
    · nlinarith
    · nlinarith [mul_le_mul_of_nonpos_right hh1 hs0.le]
  rw [e]
  rcases eq_or_lt_of_le hw1 with he | hl
  · rw [he]; nlinarith
  · nlinarith

theorem Df_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : 0 < Df p h s F := by
  have h1 : 0 < 1 + h * s := by
    rcases le_or_gt 0 s with hs0 | hs0
    · nlinarith
    · nlinarith [mul_le_mul_of_nonpos_right hh1 hs0.le]
  have e : Df p h s F = (1 - (1 - F) * p) + (1 - F) * p * (1 + h * s) := by unfold Df; ring
  have ha : 0 ≤ (1 - F) * p := by nlinarith
  have hb : (1 - F) * p ≤ 1 := by nlinarith
  rw [e]
  rcases eq_or_lt_of_le hb with he | hl
  · rw [he]; nlinarith
  · nlinarith

theorem wbar_pos' {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : 0 < wbar p h s F := by
  rw [wbar_eq]
  have hN := Nf_pos hp0 hp1 hh0 hh1 hs hF0 hF1
  have hD := Df_pos hp0 hp1 hh0 hh1 hs hF0 hF1
  rcases eq_or_lt_of_le hp0 with he | hl
  · rw [← he] at hD ⊢; simpa using hD
  · have := mul_pos hl hN
    have : 0 ≤ (1 - p) * Df p h s F := mul_nonneg (by linarith) hD.le
    linarith

/-- p′ は [0, 1] に入る。 -/
theorem p'_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) : 0 ≤ p' p h s F ∧ p' p h s F ≤ 1 := by
  have hw := wbar_pos' hp0 hp1 hh0 hh1 hs hF0 hF1
  have hN := Nf_pos hp0 hp1 hh0 hh1 hs hF0 hF1
  have hD := Df_pos hp0 hp1 hh0 hh1 hs hF0 hF1
  unfold p'
  rw [num_eq_pN]
  constructor
  · exact div_nonneg (mul_nonneg hp0 hN.le) hw.le
  · rw [div_le_one hw, wbar_eq]
    have : 0 ≤ (1 - p) * Df p h s F := mul_nonneg (by linarith) hD.le
    linarith

theorem p'_zero (h s F : ℝ) : p' 0 h s F = 0 := by unfold p' num; simp

theorem p'_one (hs : -1 < s) : p' 1 h s F = 1 := by
  have : (1 : ℝ) + s ≠ 0 := by linarith
  have e1 : num 1 h s F = 1 + s := by unfold num; ring
  have e2 : wbar 1 h s F = 1 + s := by unfold wbar; ring
  unfold p'
  rw [e1, e2, div_self this]

/-- p についての微分の分子の恒等式。 -/
theorem p_deriv_identity (p h s F : ℝ) :
    (2 * ((1 - F) * s * (1 - h)) * p + (F * (1 + s) + (1 - F) * (1 + h * s))) * wbar p h s F -
      num p h s F * (2 * ((1 - F) * s * (1 - h) - (1 - F) * h * s) * p +
        (F * (1 + s) + (1 - F) * (1 + h * s) - 1 + (1 - F) * h * s)) =
    Nf p h s F * Df p h s F +
      p * (1 - p) * s * (1 - F) * ((1 - h) * Df p h s F - h * Nf p h s F) := by
  unfold wbar num Nf Df; ring

theorem p_deriv_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : -1 < s) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 < Nf p h s F * Df p h s F +
      p * (1 - p) * s * (1 - F) * ((1 - h) * Df p h s F - h * Nf p h s F) := by
  have hN := Nf_pos hp0.le hp1.le hh0 hh1 hs hF0 hF1
  have hD := Df_pos hp0.le hp1.le hh0 hh1 hs hF0 hF1
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  have hF : 0 ≤ 1 - F := by linarith
  rcases le_or_gt 0 s with hs0 | hs0
  · -- s ≥ 0：N(D − pqs(1 − F)h) + pqs(1 − F)(1 − h)D ≥ N
    have e : Nf p h s F * Df p h s F +
        p * (1 - p) * s * (1 - F) * ((1 - h) * Df p h s F - h * Nf p h s F) =
        Nf p h s F * (1 + h * s * (1 - F) * p ^ 2) +
          p * (1 - p) * s * (1 - F) * (1 - h) * Df p h s F := by unfold Df; ring
    rw [e]
    have h1 : 0 ≤ h * s * (1 - F) * p ^ 2 := by positivity
    have h2 : 0 ≤ p * (1 - p) * s * (1 - F) * (1 - h) * Df p h s F := by
      have : 0 ≤ 1 - h := by linarith
      positivity
    nlinarith
  · -- s < 0：D(N − pqσ(1 − F)(1 − h)) + pqσ(1 − F)hN、σ = −s
    have e : Nf p h s F * Df p h s F +
        p * (1 - p) * s * (1 - F) * ((1 - h) * Df p h s F - h * Nf p h s F) =
        Df p h s F * (Nf p h s F + p * (1 - p) * s * (1 - F) * (1 - h)) +
          p * (1 - p) * (-s) * (1 - F) * h * Nf p h s F := by ring
    rw [e]
    have hk : 0 < Nf p h s F + p * (1 - p) * s * (1 - F) * (1 - h) := by
      -- = 1 + hs + s(1 − h)(F + (1 − F)(2p − p²)) ≥ 1 + s > 0
      have e2 : Nf p h s F + p * (1 - p) * s * (1 - F) * (1 - h) =
          (1 + h * s) * (1 - (F + (1 - F) * (2 * p - p ^ 2))) +
            (1 + s) * (F + (1 - F) * (2 * p - p ^ 2)) := by unfold Nf; ring
      rw [e2]
      have hw0 : 0 ≤ F + (1 - F) * (2 * p - p ^ 2) := by nlinarith
      have hw1 : F + (1 - F) * (2 * p - p ^ 2) ≤ 1 := by nlinarith [sq_nonneg (1 - p)]
      have h1 : 0 < 1 + h * s := by nlinarith [mul_le_mul_of_nonpos_right hh1 hs0.le]
      rcases eq_or_lt_of_le hw1 with he | hl
      · rw [he]; nlinarith
      · nlinarith
    have h3 : 0 ≤ p * (1 - p) * (-s) * (1 - F) * h * Nf p h s F := by
      have : 0 ≤ -s := by linarith
      positivity
    nlinarith [mul_pos hD hk]

theorem hasDerivAt_quad (a b c x : ℝ) :
    HasDerivAt (fun p => a * p ^ 2 + b * p + c) (2 * a * x + b) x := by
  have := (((hasDerivAt_pow 2 x).const_mul a).add ((hasDerivAt_id' x).const_mul b)).add_const c
  convert this using 1
  simp; ring

/-- p′ は p について [0, 1] で狭義に増える。 -/
theorem p'_strictMonoOn_p (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) : StrictMonoOn (fun p => p' p h s F) (Icc 0 1) := by
  set c2 := (1 - F) * s * (1 - h)
  set c1 := F * (1 + s) + (1 - F) * (1 + h * s)
  set k := (1 - F) * h * s
  have hnum : (fun p => num p h s F) = fun p => c2 * p ^ 2 + c1 * p + 0 := by
    ext p; unfold num; simp only [c2, c1]; ring
  have hw : (fun p => wbar p h s F) = fun p => (c2 - k) * p ^ 2 + (c1 - 1 + k) * p + 1 := by
    ext p; unfold wbar; simp only [c2, c1, k]; ring
  have hd : ∀ p, wbar p h s F ≠ 0 → HasDerivAt (fun p => p' p h s F)
      (((2 * c2 * p + c1) * wbar p h s F - num p h s F * (2 * (c2 - k) * p + (c1 - 1 + k)))
        / wbar p h s F ^ 2) p := by
    intro p hwp
    have hA : HasDerivAt (fun p => num p h s F) (2 * c2 * p + c1) p := by
      rw [hnum]; exact hasDerivAt_quad c2 c1 0 p
    have hW : HasDerivAt (fun p => wbar p h s F) (2 * (c2 - k) * p + (c1 - 1 + k)) p := by
      rw [hw]; exact hasDerivAt_quad (c2 - k) (c1 - 1 + k) 1 p
    exact hA.div hW hwp
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · intro p hp
    exact (hd p (wbar_pos' hp.1 hp.2 hh0 hh1 hs hF0 hF1).ne').continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    have hwp := wbar_pos' hp.1.le hp.2.le hh0 hh1 hs hF0 hF1
    rw [(hd p hwp.ne').deriv]
    apply div_pos _ (by positivity)
    have := p_deriv_identity p h s F
    have hpos := p_deriv_pos hp.1 hp.2 hh0 hh1 hs hF0 hF1
    simp only [c2, c1, k]
    linarith

/-- s > 0、F₁ ≤ F₂ なら、[0, 1] のどの p でも p′(F₁) ≤ p′(F₂)。 -/
theorem p'_le_of_F_le {p F₁ F₂ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : 0 < s) (hF₁ : 0 ≤ F₁) (h12 : F₁ ≤ F₂) (hF₂ : F₂ ≤ 1) :
    p' p h s F₁ ≤ p' p h s F₂ := by
  rcases eq_or_lt_of_le hp0 with he | hl
  · rw [← he, p'_zero, p'_zero]
  rcases eq_or_lt_of_le hp1 with he1 | hl1
  · rw [he1, p'_one (by linarith), p'_one (by linarith)]
  rcases eq_or_lt_of_le h12 with he2 | hl2
  · rw [he2]
  · exact ((strictMonoOn_F hl hl1 hh0 hh1 hs) ⟨hF₁, by linarith⟩ ⟨by linarith, hF₂⟩ hl2).le

end params

/-! ### 二項分布での期待値 -/

/-- 二項分布 Bin(n, x) での期待値 E[g(X)]。n 回の独立な引きを、一回目で分けて定義する。 -/
noncomputable def binE : ℕ → (ℕ → ℝ) → ℝ → ℝ
  | 0, g, _ => g 0
  | n + 1, g, x => x * binE n (fun j => g (j + 1)) x + (1 - x) * binE n g x

/-- 定義は二項分布の式 Σ C(n, j) x^j (1 − x)^(n−j) g(j) と同じ。 -/
theorem binE_eq_sum (n : ℕ) : ∀ (g : ℕ → ℝ) (x : ℝ),
    binE n g x =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) * g j := by
  induction n with
  | zero => intro g x; simp [binE]
  | succ n ih =>
    intro g x
    rw [binE, ih, ih, Finset.sum_range_succ' _ (n + 1)]
    simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, one_mul, Nat.sub_zero, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ (fun j => (n.choose (j + 1) : ℝ) * x ^ (j + 1) *
      (1 - x) ^ (n + 1 - (j + 1)) * g (j + 1)), Nat.choose_succ_self, Nat.cast_zero,
      zero_mul, zero_mul, zero_mul, add_zero]
    rw [Finset.sum_range_succ' (fun j => (n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) * g j)]
    rw [Finset.mul_sum, mul_add, Finset.mul_sum]
    have h1 : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * x ^ (j + 1) *
        (1 - x) ^ (n + 1 - (j + 1)) * g (j + 1) =
        x * ((n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j) * g (j + 1)) := by
      intro j _
      rw [show n + 1 - (j + 1) = n - j by omega]; ring
    have h2 : ∀ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) * x ^ (j + 1) *
        (1 - x) ^ (n + 1 - (j + 1)) * g (j + 1) =
        (1 - x) * ((n.choose (j + 1) : ℝ) * x ^ (j + 1) * (1 - x) ^ (n - (j + 1)) * g (j + 1)) := by
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      rw [show n + 1 - (j + 1) = (n - (j + 1)) + 1 by omega, pow_succ]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero, pow_succ]
    ring

theorem binE_one (n : ℕ) : ∀ g : ℕ → ℝ, binE n g 1 = g n := by
  induction n with
  | zero => intro g; rfl
  | succ n ih => intro g; simp [binE, ih]

theorem binE_mono_g (n : ℕ) : ∀ (g g' : ℕ → ℝ) (x : ℝ), 0 ≤ x → x ≤ 1 → (∀ j, g j ≤ g' j) →
    binE n g x ≤ binE n g' x := by
  induction n with
  | zero => intro g g' x _ _ hg; exact hg 0
  | succ n ih =>
    intro g g' x hx0 hx1 hg
    simp only [binE]
    have h1 := ih (fun j => g (j + 1)) (fun j => g' (j + 1)) x hx0 hx1 (fun j => hg (j + 1))
    have h2 := ih g g' x hx0 hx1 hg
    have : 0 ≤ 1 - x := by linarith
    nlinarith

theorem binE_bounds (n : ℕ) : ∀ (g : ℕ → ℝ) (x : ℝ), 0 ≤ x → x ≤ 1 →
    (∀ j, 0 ≤ g j ∧ g j ≤ 1) → 0 ≤ binE n g x ∧ binE n g x ≤ 1 := by
  induction n with
  | zero => intro g x _ _ hg; exact hg 0
  | succ n ih =>
    intro g x hx0 hx1 hg
    simp only [binE]
    obtain ⟨a0, a1⟩ := ih (fun j => g (j + 1)) x hx0 hx1 (fun j => hg (j + 1))
    obtain ⟨b0, b1⟩ := ih g x hx0 hx1 hg
    have : 0 ≤ 1 - x := by linarith
    constructor <;> nlinarith

/-- g が増える関数なら、期待値は x について増える（二項分布の単調性）。 -/
theorem binE_mono_x (n : ℕ) : ∀ (g : ℕ → ℝ) (x y : ℝ), Monotone g → 0 ≤ x → x ≤ y → y ≤ 1 →
    binE n g x ≤ binE n g y := by
  induction n with
  | zero => intro g x y _ _ _ _; exact le_rfl
  | succ n ih =>
    intro g x y hg hx0 hxy hy1
    simp only [binE]
    have hg1 : Monotone fun j => g (j + 1) := fun a b hab => hg (by omega)
    have h1 := ih (fun j => g (j + 1)) x y hg1 hx0 hxy hy1
    have h2 := ih g x y hg hx0 hxy hy1
    have h3 := binE_mono_g n g (fun j => g (j + 1)) x hx0 (by linarith)
      (fun j => hg (Nat.le_succ j))
    have hy0 : 0 ≤ y := by linarith
    have : 0 ≤ 1 - y := by linarith
    nlinarith

/-! ### ライト＝フィッシャー模型の固定する確率 -/

/-- 写し M 個の集団で A の写しが i 個のとき、n 世代のうちに固定している確率
（次の世代の写しの数は Bin(M, p′(i/M))。i > M は M と同じに扱う）。 -/
noncomputable def fixBy (M : ℕ) (h s F : ℝ) : ℕ → ℕ → ℝ
  | 0, i => if M ≤ i then 1 else 0
  | n + 1, i => binE M (fixBy M h s F n) (p' ((min i M : ℕ) / (M : ℝ)) h s F)

section chain

variable {M : ℕ} {h s F : ℝ}

theorem frac_mem (hM : 0 < M) (i : ℕ) :
    0 ≤ ((min i M : ℕ) : ℝ) / M ∧ ((min i M : ℕ) : ℝ) / M ≤ 1 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · positivity
  · rw [div_le_one hM']; exact_mod_cast min_le_right i M

theorem frac_mono (hM : 0 < M) : Monotone fun i : ℕ => ((min i M : ℕ) : ℝ) / M := by
  intro a b hab
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  apply div_le_div_of_nonneg_right _ hM'.le
  exact_mod_cast min_le_min_right M hab

theorem fixBy_bounds (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (n : ℕ) : ∀ i, 0 ≤ fixBy M h s F n i ∧ fixBy M h s F n i ≤ 1 := by
  induction n with
  | zero => intro i; simp only [fixBy]; split_ifs <;> norm_num
  | succ n ih =>
    intro i
    obtain ⟨x0, x1⟩ := frac_mem hM i
    obtain ⟨y0, y1⟩ := p'_mem x0 x1 hh0 hh1 hs hF0 hF1
    exact binE_bounds M _ _ y0 y1 ih

theorem fixBy_mono_i (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (n : ℕ) : Monotone (fixBy M h s F n) := by
  induction n with
  | zero =>
    intro a b hab
    simp only [fixBy]
    split_ifs with h1 h2 <;> norm_num
    exact absurd (h1.trans hab) h2
  | succ n ih =>
    intro a b hab
    obtain ⟨xa0, xa1⟩ := frac_mem hM a
    obtain ⟨xb0, xb1⟩ := frac_mem hM b
    have hx := frac_mono hM hab
    have hp := (p'_strictMonoOn_p hh0 hh1 hs hF0 hF1).monotoneOn ⟨xa0, xa1⟩ ⟨xb0, xb1⟩ hx
    obtain ⟨y0, _⟩ := p'_mem xa0 xa1 hh0 hh1 hs hF0 hF1
    obtain ⟨_, y1⟩ := p'_mem xb0 xb1 hh0 hh1 hs hF0 hF1
    exact binE_mono_x M _ _ _ ih y0 hp y1

/-- 固定は戻らないので、n 世代のうちに固定している確率は n について増える。 -/
theorem fixBy_mono_n (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (n : ℕ) : ∀ i, fixBy M h s F n i ≤ fixBy M h s F (n + 1) i := by
  induction n with
  | zero =>
    intro i
    by_cases hi : M ≤ i
    · have hmin : min i M = M := min_eq_right hi
      have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      simp only [fixBy, hi, ite_true, hmin, div_self hM', p'_one hs, binE_one, le_refl]
    · simp only [fixBy, hi, ite_false]
      exact (fixBy_bounds hM hh0 hh1 hs hF0 hF1 1 i).1
  | succ n ih =>
    intro i
    obtain ⟨x0, x1⟩ := frac_mem hM i
    obtain ⟨y0, y1⟩ := p'_mem x0 x1 hh0 hh1 hs hF0 hF1
    exact binE_mono_g M _ _ _ y0 y1 ih

/-- 有利な変異（s > 0）、0 ≤ h ≤ 1 なら、どの世代までの固定の確率も F について減らない。 -/
theorem fixBy_mono_F (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : 0 < s) {F₁ F₂ : ℝ}
    (hF₁ : 0 ≤ F₁) (h12 : F₁ ≤ F₂) (hF₂ : F₂ ≤ 1) (n : ℕ) :
    ∀ i, fixBy M h s F₁ n i ≤ fixBy M h s F₂ n i := by
  induction n with
  | zero => intro i; exact le_rfl
  | succ n ih =>
    intro i
    obtain ⟨x0, x1⟩ := frac_mem hM i
    have hs' : -1 < s := by linarith
    obtain ⟨y0, y1⟩ := p'_mem x0 x1 hh0 hh1 hs' hF₁ (h12.trans hF₂)
    obtain ⟨z0, z1⟩ := p'_mem x0 x1 hh0 hh1 hs' (hF₁.trans h12) hF₂
    have hyz := p'_le_of_F_le x0 x1 hh0 hh1 hs hF₁ h12 hF₂
    simp only [fixBy]
    calc binE M (fixBy M h s F₁ n) (p' _ h s F₁)
        ≤ binE M (fixBy M h s F₂ n) (p' _ h s F₁) := binE_mono_g M _ _ _ y0 y1 ih
      _ ≤ binE M (fixBy M h s F₂ n) (p' _ h s F₂) :=
          binE_mono_x M _ _ _ (fixBy_mono_i hM hh0 hh1 hs' (hF₁.trans h12) hF₂ n) y0 hyz z1

/-- 固定する確率 = n → ∞ での極限（n について増えて 1 以下なので収束する）。 -/
noncomputable def fixProb (M : ℕ) (h s F : ℝ) (i : ℕ) : ℝ := ⨆ n, fixBy M h s F n i

theorem fixBy_tendsto (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : -1 < s) (hF0 : 0 ≤ F)
    (hF1 : F ≤ 1) (i : ℕ) :
    Filter.Tendsto (fun n => fixBy M h s F n i) Filter.atTop (nhds (fixProb M h s F i)) := by
  apply tendsto_atTop_ciSup
  · exact monotone_nat_of_le_succ (fun n => fixBy_mono_n hM hh0 hh1 hs hF0 hF1 n i)
  · exact ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (fixBy_bounds hM hh0 hh1 hs hF0 hF1 n i).2⟩

/-- 原稿の芯：有利な変異（s > 0）、0 ≤ h ≤ 1 なら、どの写しの数 M でも、固定する確率は F について
減らない（F₁ ≤ F₂ ⇒ u_{F₁}(i) ≤ u_{F₂}(i)、一つの写しからなら i = 1）。 -/
theorem fixProb_mono_F (hM : 0 < M) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hs : 0 < s) {F₁ F₂ : ℝ}
    (hF₁ : 0 ≤ F₁) (h12 : F₁ ≤ F₂) (hF₂ : F₂ ≤ 1) (i : ℕ) :
    fixProb M h s F₁ i ≤ fixProb M h s F₂ i := by
  have hs' : -1 < s := by linarith
  exact le_of_tendsto_of_tendsto' (fixBy_tendsto hM hh0 hh1 hs' hF₁ (h12.trans hF₂) i)
    (fixBy_tendsto hM hh0 hh1 hs' (hF₁.trans h12) hF₂ i)
    (fun n => fixBy_mono_F hM hh0 hh1 hs hF₁ h12 hF₂ n i)

/-- F = 1 では、固定する確率は h によらない（半数体の模型と同じ遷移）。 -/
theorem fixBy_full (M : ℕ) (h h₂ s : ℝ) (n : ℕ) : fixBy M h s 1 n = fixBy M h₂ s 1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext i
    simp only [fixBy, ih, full_inbreeding]

theorem fixProb_full (M : ℕ) (h h₂ s : ℝ) (i : ℕ) : fixProb M h s 1 i = fixProb M h₂ s 1 i := by
  unfold fixProb; simp only [fixBy_full M h h₂ s]

end chain

end Paper984

end Yamagishi
