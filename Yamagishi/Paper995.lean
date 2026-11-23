/-
論文995『分裂の破片に質量があると取り出せる割合は下がり、落ちる破片の重さがより強く効く』の格上げ
（芯だけ）。

日本語の一文：赤道面の折り返しの点で、質量 1 の粒子が質量 μ₁（外へ出る）と μ₂（落ちる）の破片に割れる
とき、取り出せる割合の最大は η = ½[√λ·√(2/r) − (1 + μ₂² − μ₁²)] で、回転 a にも角運動量にもよらない。
English: Core only: at an equatorial turning point, in the rest frame of the decaying particle
(mass 1, energy 1 at infinity), with the Killing vector ∂_t having components (1, ξ¹), (ξ¹)² = 2/r,
the largest extracted share over all two-body splits into masses μ₁ (out) and μ₂ (in) is
η = ½[√λ·√(2/r) − (1 + μ₂² − μ₁²)], λ = 1 + μ₁⁴ + μ₂⁴ − 2μ₁² − 2μ₂² − 2μ₁²μ₂²; it does not depend on
the spin a; equal masses give ½(√((2/r)(1 − 4μ²)) − 1) > 0 iff μ < ½√(1 − r/2); swapping the masses
changes η by μ₁² − μ₂²; negative energy needs r < 2.

原稿（995_yamagishi_massive_fragments_lower_the_share_extracted_in_one_split/…_jp.tex）は、回転 1 と
0.9 の六つの半径で、保存則と質量の殻の条件を数値で解き（L₂ を刻んで二分法）、同じ質量の 18 点で
½(√((2/r)(1 − 4μ²)) − 1) と一致することを確かめ、非対称な四つの組を並べる。式は導いておらず、
非対称な場合の形は「探していない」と書いている。

ここで証明した言明（r > 0、0 ≤ μ₁, μ₂、ξ¹² = 2/r）：
  (1) `split_energies`：保存則と質量の殻から、落ちる破片の静止系のエネルギーは (1 + μ₂² − μ₁²)/2、
      運動量の二乗は λ/4 に決まる。
  (2) `share_le`：どの分裂でも、取り出した割合 E₁ − 1 ≤ η_max(μ₁, μ₂, r)。
      `share_attained`：μ₁ + μ₂ < 1 なら等号を与える分裂が在る。式に a は入らない。
  (3) `equal_mass`：μ₁ = μ₂ = μ で η_max = ½(√((2/r)(1 − 4μ²)) − 1)（光子 μ = 0 で ½(√(2/r) − 1)）。
      `equal_mass_pos_iff`：r < 2、0 ≤ μ で、η_max > 0 ⇔ μ < ½√(1 − r/2)。
  (4) `swap`：η_max(μ₁, μ₂) − η_max(μ₂, μ₁) = μ₁² − μ₂²（重さは落ちる側にあるほど割合を下げる）。
      `paper_pair`：原稿の 0.188435 − 0.098435 = 0.09 = 0.3² はこの差そのもの。
  (5) `negative_energy_needs`：未来向きの破片のエネルギー e − kξ¹ が負になれば r < 2。
      `photon_negative_iff`：光子なら、負のエネルギーが作れる ⇔ r < 2（エルゴ球）。
足した仮定（ここが「芯だけ」の理由）：折り返しの点では三つの運動量が t と φ の張る二次元の面にあり、
その面が地平線の外でローレンツ型であること、壊れる粒子の静止系の正規直交の基底でキリングベクトル ∂_t の
成分が (E₀, ξ¹) = (1, ξ¹)、その長さの二乗が g_tt = −(1 − 2/r)（よって ξ¹² = 2/r）であることを、物理の
入力として置いた。保存されるエネルギーは E = −⟨p, ∂_t⟩ = e − kξ¹ と書いた。
形式化していないもの：落ちてくる粒子が届くか・外へ出る破片が逃げるか（論文939 のファイルで一部）、
赤道面の外、原稿の数値の解き方、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper995

open Real

/-- 分裂：静止系の成分。破片 1（外へ出る）は (e₁, k₁)、破片 2（落ちる）は (e₂, k₂)。 -/
structure Split (μ₁ μ₂ : ℝ) where
  e1 : ℝ
  k1 : ℝ
  e2 : ℝ
  k2 : ℝ
  shell1 : e1 ^ 2 - k1 ^ 2 = μ₁ ^ 2
  shell2 : e2 ^ 2 - k2 ^ 2 = μ₂ ^ 2
  fut1 : 0 < e1
  fut2 : 0 < e2
  cons0 : e1 + e2 = 1
  cons1 : k1 + k2 = 0

/-- λ = 1 + μ₁⁴ + μ₂⁴ − 2μ₁² − 2μ₂² − 2μ₁²μ₂²。 -/
def lam (μ₁ μ₂ : ℝ) : ℝ := 1 + μ₁ ^ 4 + μ₂ ^ 4 - 2 * μ₁ ^ 2 - 2 * μ₂ ^ 2 - 2 * μ₁ ^ 2 * μ₂ ^ 2

/-- 取り出せる割合の最大 η_max = ½[√λ·√(2/r) − (1 + μ₂² − μ₁²)]。 -/
noncomputable def etaMax (μ₁ μ₂ r : ℝ) : ℝ :=
  (√(lam μ₁ μ₂) * √(2 / r) - (1 + μ₂ ^ 2 - μ₁ ^ 2)) / 2

/-- 破片 1 の取り出した割合 η = E₁ − E₀（E₀ = 1、E₁ = e₁ − k₁ξ¹）。 -/
def share {μ₁ μ₂ : ℝ} (S : Split μ₁ μ₂) (ξ : ℝ) : ℝ := S.e1 - S.k1 * ξ - 1

/-- (1) 落ちる破片のエネルギーと運動量の二乗は決まる。 -/
theorem split_energies {μ₁ μ₂ : ℝ} (S : Split μ₁ μ₂) :
    S.e2 = (1 + μ₂ ^ 2 - μ₁ ^ 2) / 2 ∧ S.k2 ^ 2 = lam μ₁ μ₂ / 4 := by
  have h1 := S.shell1
  have h2 := S.shell2
  have c0 : S.e1 = 1 - S.e2 := by linarith [S.cons0]
  have c1 : S.k1 = -S.k2 := by linarith [S.cons1]
  rw [c0, c1] at h1
  have he : S.e2 = (1 + μ₂ ^ 2 - μ₁ ^ 2) / 2 := by nlinarith
  refine ⟨he, ?_⟩
  have : S.k2 ^ 2 = S.e2 ^ 2 - μ₂ ^ 2 := by linarith
  rw [this, he]
  unfold lam
  ring

/-- 取り出した割合は −E₂（E₂ = e₂ − k₂ξ¹）。 -/
theorem share_eq {μ₁ μ₂ : ℝ} (S : Split μ₁ μ₂) (ξ : ℝ) : share S ξ = -(S.e2 - S.k2 * ξ) := by
  unfold share
  have c0 : S.e1 = 1 - S.e2 := by linarith [S.cons0]
  have c1 : S.k1 = -S.k2 := by linarith [S.cons1]
  rw [c0, c1]; ring

/-- (2) どの分裂でも、取り出した割合は η_max 以下。 -/
theorem share_le {μ₁ μ₂ r ξ : ℝ} (hξ : ξ ^ 2 = 2 / r) (S : Split μ₁ μ₂) :
    share S ξ ≤ etaMax μ₁ μ₂ r := by
  obtain ⟨he, hk⟩ := split_energies S
  rw [share_eq, he]
  unfold etaMax
  have hlam : 0 ≤ lam μ₁ μ₂ := by nlinarith [sq_nonneg S.k2, hk]
  have habsk : |S.k2| = √(lam μ₁ μ₂) / 2 := by
    rw [← sqrt_sq_eq_abs, hk, sqrt_div hlam, show (4 : ℝ) = 2 ^ 2 by norm_num,
      sqrt_sq (by norm_num)]
  have habsξ : |ξ| = √(2 / r) := by rw [← sqrt_sq_eq_abs, hξ]
  have : S.k2 * ξ ≤ |S.k2| * |ξ| := by rw [← abs_mul]; exact le_abs_self _
  rw [habsk, habsξ] at this
  linarith

/-- (2) μ₁ + μ₂ < 1 なら、等号を与える分裂が在る（式に回転 a は入らない）。 -/
theorem share_attained {μ₁ μ₂ r ξ : ℝ} (hξ : ξ ^ 2 = 2 / r) (h1 : 0 ≤ μ₁)
    (h2 : 0 ≤ μ₂) (h12 : μ₁ + μ₂ < 1) :
    ∃ S : Split μ₁ μ₂, share S ξ = etaMax μ₁ μ₂ r := by
  have hlam : 0 ≤ lam μ₁ μ₂ := by
    have : lam μ₁ μ₂ = (1 - (μ₁ + μ₂) ^ 2) * (1 - (μ₁ - μ₂) ^ 2) := by unfold lam; ring
    rw [this]
    apply mul_nonneg <;> nlinarith
  set σ : ℝ := if 0 ≤ ξ then 1 else -1 with hσ
  have hσξ : σ * ξ = |ξ| := by
    simp only [hσ]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · push Not at h; rw [abs_of_neg h]; ring
  have hσ2 : σ ^ 2 = 1 := by simp only [hσ]; split_ifs <;> norm_num
  set k : ℝ := σ * √(lam μ₁ μ₂) / 2
  have hk2 : k ^ 2 = lam μ₁ μ₂ / 4 := by
    simp only [k]; rw [div_pow, mul_pow, hσ2, sq_sqrt hlam]; ring
  have hμ1 : μ₁ < 1 := by linarith
  have hμ2 : μ₂ < 1 := by linarith
  refine ⟨⟨(1 + μ₁ ^ 2 - μ₂ ^ 2) / 2, -k, (1 + μ₂ ^ 2 - μ₁ ^ 2) / 2, k, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [neg_sq, hk2]; unfold lam; ring
  · rw [hk2]; unfold lam; ring
  · nlinarith
  · nlinarith
  · ring
  · ring
  · show (1 + μ₁ ^ 2 - μ₂ ^ 2) / 2 - -k * ξ - 1 = etaMax μ₁ μ₂ r
    unfold etaMax
    have hk : k * ξ = √(lam μ₁ μ₂) / 2 * |ξ| := by
      simp only [k]; rw [← hσξ]; ring
    have habsξ : |ξ| = √(2 / r) := by rw [← sqrt_sq_eq_abs, hξ]
    rw [show (1 + μ₁ ^ 2 - μ₂ ^ 2) / 2 - -k * ξ - 1 = k * ξ - (1 + μ₂ ^ 2 - μ₁ ^ 2) / 2 by ring,
      hk, habsξ]
    ring

/-- (3) 同じ質量：η_max = ½(√((2/r)(1 − 4μ²)) − 1)。 -/
theorem equal_mass (μ r : ℝ) (hμ : 4 * μ ^ 2 ≤ 1) :
    etaMax μ μ r = (√(2 / r * (1 - 4 * μ ^ 2)) - 1) / 2 := by
  unfold etaMax
  have : lam μ μ = 1 - 4 * μ ^ 2 := by unfold lam; ring
  rw [this, sqrt_mul' (2 / r) (by linarith : (0 : ℝ) ≤ 1 - 4 * μ ^ 2)]
  ring

/-- (3) r < 2、0 ≤ μ で、η_max > 0 ⇔ μ < ½√(1 − r/2)。 -/
theorem equal_mass_pos_iff {μ r : ℝ} (hμ0 : 0 ≤ μ) (hr : 0 < r) (hr2 : r < 2) :
    0 < etaMax μ μ r ↔ μ < √(1 - r / 2) / 2 := by
  have hs : 0 < 1 - r / 2 := by linarith
  constructor
  · intro h
    by_cases hμ : 4 * μ ^ 2 ≤ 1
    · rw [equal_mass μ r hμ] at h
      have h1 : 1 < √(2 / r * (1 - 4 * μ ^ 2)) := by linarith
      have h2 : 1 < 2 / r * (1 - 4 * μ ^ 2) := by
        by_contra hc; push Not at hc
        have := sqrt_le_sqrt hc; rw [sqrt_one] at this; linarith
      have h3 : r / 2 < 1 - 4 * μ ^ 2 := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hr] at h2; linarith
      rw [lt_div_iff₀ (by norm_num), lt_sqrt (by linarith)]
      nlinarith
    · exfalso
      push Not at hμ
      unfold etaMax at h
      have : lam μ μ = 1 - 4 * μ ^ 2 := by unfold lam; ring
      rw [this, sqrt_eq_zero'.mpr (by linarith)] at h
      linarith
  · intro h
    have h1 : 2 * μ < √(1 - r / 2) := by linarith
    have h2 : 4 * μ ^ 2 < 1 - r / 2 := by
      have := (lt_sqrt (by linarith)).mp h1; nlinarith
    rw [equal_mass μ r (by linarith)]
    have h3 : 1 < 2 / r * (1 - 4 * μ ^ 2) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hr]; linarith
    have : 1 < √(2 / r * (1 - 4 * μ ^ 2)) := by
      rw [lt_sqrt (by norm_num)]; linarith
    linarith

/-- (4) 質量の入れ替え：η_max(μ₁, μ₂) − η_max(μ₂, μ₁) = μ₁² − μ₂²。 -/
theorem swap (μ₁ μ₂ r : ℝ) : etaMax μ₁ μ₂ r - etaMax μ₂ μ₁ r = μ₁ ^ 2 - μ₂ ^ 2 := by
  unfold etaMax
  have : lam μ₂ μ₁ = lam μ₁ μ₂ := by unfold lam; ring
  rw [this]
  ring

/-- (4) 原稿の組：0.188435 − 0.098435 = 0.09 は、外へ出る破片に 0.3 を持たせたときと落ちる破片に
持たせたときの差 0.3² そのもの（どの r でも）。 -/
theorem paper_pair (r : ℝ) : etaMax 0.3 0 r - etaMax 0 0.3 r = 0.09 ∧
    (0.188435 : ℝ) - 0.098435 = 0.09 := by
  constructor
  · rw [swap]; norm_num
  · norm_num

/-- (5) 未来向き（e > 0、e² − k² ≥ 0）の破片のエネルギー e − kξ¹ が負なら r < 2。 -/
theorem negative_energy_needs {e k r ξ : ℝ} (hr : 0 < r) (hξ : ξ ^ 2 = 2 / r) (he : 0 < e)
    (hc : k ^ 2 ≤ e ^ 2) (hE : e - k * ξ < 0) : r < 2 := by
  have h1 : e < k * ξ := by linarith
  have h2 : (k * ξ) ^ 2 ≤ e ^ 2 * ξ ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have h3 : e ^ 2 < (k * ξ) ^ 2 := by nlinarith
  have h4 : 1 < ξ ^ 2 := by
    have : e ^ 2 * 1 < e ^ 2 * ξ ^ 2 := by linarith
    exact lt_of_mul_lt_mul_left this (by positivity)
  rw [hξ, lt_div_iff₀ hr] at h4
  linarith

/-- (5) 光子なら、負のエネルギーが作れる ⇔ r < 2。 -/
theorem photon_negative_iff {r ξ : ℝ} (hr : 0 < r) (hξ : ξ ^ 2 = 2 / r) :
    (∃ e k : ℝ, 0 < e ∧ e ^ 2 - k ^ 2 = 0 ∧ e - k * ξ < 0) ↔ r < 2 := by
  constructor
  · rintro ⟨e, k, he, hc, hE⟩
    exact negative_energy_needs hr hξ he (by linarith) hE
  · intro h
    have h4 : 1 < ξ ^ 2 := by rw [hξ, lt_div_iff₀ hr]; linarith
    have habs : 1 < |ξ| := by
      have : (1 : ℝ) ^ 2 < |ξ| ^ 2 := by rw [sq_abs]; linarith
      exact (pow_lt_pow_iff_left₀ (by norm_num) (abs_nonneg _) two_ne_zero).mp this
    rcases le_or_gt 0 ξ with hξ0 | hξ0
    · refine ⟨1, 1, one_pos, by norm_num, ?_⟩
      rw [abs_of_nonneg hξ0] at habs; linarith
    · refine ⟨1, -1, one_pos, by norm_num, ?_⟩
      rw [abs_of_neg hξ0] at habs; linarith

end Paper995

end Yamagishi
