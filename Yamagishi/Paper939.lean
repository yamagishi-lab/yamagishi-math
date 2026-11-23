/-
論文939『一回の分裂で得られる割合の式は、落ちてくる粒子がそこまで届くかを問わない』の格上げ（芯だけ）。

日本語の一文：回転 a のカー時空の赤道面で、遠くから静止して落ちた粒子が地平面の外で折り返せるのは
r > r_mb = 2 − a + 2√(1 − a) の点だけで、そこがエルゴ球（r < 2）に入るのは a > 2√2 − 2 のときに限る。
English: Core only: with the E = 1 equatorial Kerr radial function Q_L(r) = 2r² − L²r + 2(L − a)²
taken as input, a particle falling from rest at infinity can have its outer turning point at r₀
outside the horizon only if r₀ ≥ r_mb = 2 − a + 2√(1 − a) (r₀ = r_mb only as a double root); every
r₀ > r_mb is such a turning point; r_mb < 2 iff a > 2√2 − 2; and the photon-split gain
½(√(2/r) − 1) on reachable points stays below its value at r_mb, which is below the horizon value
when a < 1.

原稿（939_yamagishi_the_gain_formula_in_one_split_does_not_ask_whether_the_particle_can_arrive/
…_jp.tex）は、a = 0.5・0.9・0.99・0.999・1 の五つで、その場の条件だけの最大を式と突き合わせ、届く分裂を
半径 400 点・外の 4000 点の格子で探している。a = 0.5 は「見つからなかった。無いとは言い切らない」。

ここで証明した言明（質量 1、0 ≤ a ≤ 1、x = √r₀）：
  (1) `outer_root_le`：r₀ が遠くから来た粒子の折り返しの点（Q_L(r₀) = 0 で r > r₀ では Q_L(r) > 0）なら
      L² ≤ 4r₀。
  (2) `no_turning_point`：地平面 r_H = 1 + √(1 − a²) の外で r₀ < r_mb なら、L² ≤ 4r₀ のどの L でも
      Q_L(r₀) > 0。`not_turning`：よって、そこはどの L でも折り返しの点にならない。
  (3) `rmb_double_root`：a < 1 で r₀ = r_mb なら、折り返せる L は L² = 4r_mb（L = L_mb = 2 + 2√(1 − a)）
      だけで、そこは二重根（Q′ = 0、有限の時間では届かない）。
  (4) `turning_point_exists`：r₀ > r_mb ならどこでも、0 < L、L² < 4r₀ の L で単根の折り返しの点になる。
  (5) `rmb_lt_two_iff`：r_mb < 2 ⇔ a > 2√2 − 2。a = 0.5 では届く点はエルゴ球に入らない（`half_not`）。
  (6) `gain_reachable_lt`：その場の得 ½(√(2/r) − 1) は r について減り、届く点 r > r_mb では r_mb での値
      より真に小さい。`rH_lt_rmb`・`gain_rmb_lt_rH`：a < 1 なら r_H < r_mb なので、その値は地平面の
      値より真に小さい（`rH_one`：a = 1 では r_H = r_mb = 1 で一致）。
足した仮定（ここが「芯だけ」の理由）：E = 1 の赤道面の動径の式 r³(dr/dτ)² = r·Q_L(r) を定義として置いた。
その場の得の式 ½(√(2/r) − 1)（光子二つに割れるときの最大）は既知の式として置いた（質量のある破片を含む
導き方は論文995 のファイルにある）。負のエネルギーの光子がエルゴ球の中だけで作れることも、そこで扱う。
形式化していないもの：出ていく光子が無限遠へ逃げるか、原稿の格子の探索の数、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper939

open Real

/-- E = 1 の赤道面の動径の式の芯 Q_L(r) = 2r² − L²r + 2(L − a)²（r³(dr/dτ)² = r·Q_L(r)）。 -/
def Q (a L r : ℝ) : ℝ := 2 * r ^ 2 - L ^ 2 * r + 2 * (L - a) ^ 2

/-- 地平面の半径 r_H = 1 + √(1 − a²)。 -/
noncomputable def rH (a : ℝ) : ℝ := 1 + √(1 - a ^ 2)

/-- ぎりぎり束縛の円軌道の半径 r_mb = 2 − a + 2√(1 − a) = (1 + √(1 − a))²。 -/
noncomputable def rmb (a : ℝ) : ℝ := 2 - a + 2 * √(1 - a)

/-- 遠くから来た粒子の折り返しの点：Q_L(r₀) = 0 で、それより外では Q_L > 0。 -/
def IsTurning (a L r₀ : ℝ) : Prop := Q a L r₀ = 0 ∧ ∀ r, r₀ < r → 0 < Q a L r

theorem rmb_eq {a : ℝ} (ha1 : a ≤ 1) : rmb a = (1 + √(1 - a)) ^ 2 := by
  unfold rmb
  have := sq_sqrt (show 0 ≤ 1 - a by linarith)
  nlinarith

/-- (1) 折り返しの点なら L² ≤ 4r₀。 -/
theorem outer_root_le {a L r₀ : ℝ} (h : IsTurning a L r₀) : L ^ 2 ≤ 4 * r₀ := by
  by_contra hc
  push Not at hc
  set k := (L ^ 2 - 4 * r₀) / 4
  have hk : 0 < k := by simp only [k]; linarith
  have := h.2 (r₀ + k) (by linarith)
  have e : Q a L (r₀ + k) = Q a L r₀ + k * (4 * r₀ - L ^ 2) + 2 * k ^ 2 := by unfold Q; ring
  rw [e, h.1] at this
  have : 4 * r₀ - L ^ 2 = -4 * k := by simp only [k]; ring
  nlinarith

/-- G(L) − G(2x) の因数分解（x² = r₀）。 -/
theorem Q_sub_Q_top (a L x : ℝ) :
    Q a L (x ^ 2) - Q a (2 * x) (x ^ 2) = (2 * x - L) * (4 * a - (2 - x ^ 2) * (L + 2 * x)) := by
  unfold Q; ring

/-- Q を L = ±2x の値で補間した形（x² = r₀、x ≠ 0）。 -/
theorem Q_interp (a L x : ℝ) (hx : x ≠ 0) :
    Q a L (x ^ 2) = (Q a (2 * x) (x ^ 2) * (L + 2 * x) + Q a (-(2 * x)) (x ^ 2) * (2 * x - L))
      / (4 * x) + (2 - x ^ 2) * (L ^ 2 - 4 * x ^ 2) := by
  unfold Q; field_simp; ring

theorem Q_top (a x : ℝ) :
    Q a (2 * x) (x ^ 2) = -2 * (x ^ 2 - 2 * x + a) * (x ^ 2 + 2 * x - a) := by unfold Q; ring

theorem Q_bot (a x : ℝ) :
    Q a (-(2 * x)) (x ^ 2) = -2 * (x ^ 2 - 2 * x - a) * (x ^ 2 + 2 * x + a) := by unfold Q; ring

/-- 地平面の外（r₀ > r_H）では r₀² − 2r₀ + a² > 0 で r₀ > 1。 -/
theorem outside_horizon {a r₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h : rH a < r₀) :
    0 < r₀ ^ 2 - 2 * r₀ + a ^ 2 ∧ 1 < r₀ := by
  unfold rH at h
  have hs := sqrt_nonneg (1 - a ^ 2)
  have hsq := sq_sqrt (show 0 ≤ 1 - a ^ 2 by nlinarith)
  constructor
  · nlinarith
  · linarith

/-- a ≥ x(2 − x²)（地平面の外で x² < 2 のとき。頂点 L* = 2a/(2 − x²) が 2x より右にある）。 -/
theorem vertex_right {a x : ℝ} (ha0 : 0 ≤ a) (hx1 : 1 < x) (hx2 : x ^ 2 < 2)
    (hΔ : 0 < (x ^ 2) ^ 2 - 2 * x ^ 2 + a ^ 2) : x * (2 - x ^ 2) < a := by
  have h1 : 0 < 2 - x ^ 2 := by linarith
  have h2 : 2 - x ^ 2 < 1 := by nlinarith
  have h3 : x ^ 2 * (2 - x ^ 2) < a ^ 2 := by nlinarith
  have h4 : (x * (2 - x ^ 2)) ^ 2 < a ^ 2 := by
    have : (x * (2 - x ^ 2)) ^ 2 = x ^ 2 * (2 - x ^ 2) * (2 - x ^ 2) := by ring
    rw [this]
    have : x ^ 2 * (2 - x ^ 2) * (2 - x ^ 2) ≤ x ^ 2 * (2 - x ^ 2) := by
      have : 0 < x ^ 2 * (2 - x ^ 2) := by positivity
      nlinarith
    linarith
  have : 0 ≤ x * (2 - x ^ 2) := by positivity
  exact (pow_lt_pow_iff_left₀ this ha0 two_ne_zero).mp h4

/-- (2) 地平面の外で r₀ < r_mb なら、L² ≤ 4r₀ のどの L でも Q_L(r₀) > 0。 -/
theorem no_turning_point {a L r₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hH : rH a < r₀)
    (hmb : r₀ < rmb a) (hL : L ^ 2 ≤ 4 * r₀) : 0 < Q a L r₀ := by
  obtain ⟨hΔ, hr1⟩ := outside_horizon ha0 ha1 hH
  set x := √r₀ with hx_def
  have hr0 : 0 < r₀ := by linarith
  have hx2 : x ^ 2 = r₀ := sq_sqrt hr0.le
  have hx0 : 0 < x := sqrt_pos.mpr hr0
  have hx1 : 1 < x := by
    rw [hx_def, show (1 : ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) hr1
  set s := √(1 - a) with hs_def
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - a := sq_sqrt (by linarith)
  have hxs : x < 1 + s := by
    rw [rmb_eq ha1] at hmb
    have : x ^ 2 < (1 + s) ^ 2 := by rw [hx2]; exact hmb
    nlinarith
  have hLx : |L| ≤ 2 * x := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 * x)]
    apply sq_le_sq.mp
    nlinarith
  have hL1 := (abs_le.mp hLx).1
  have hL2 := (abs_le.mp hLx).2
  -- G(2x) > 0、G(−2x) > 0
  have hP : x ^ 2 - 2 * x + a < 0 := by nlinarith
  have htop : 0 < Q a (2 * x) (x ^ 2) := by rw [Q_top]; nlinarith
  have hbot : 0 < Q a (-(2 * x)) (x ^ 2) := by
    rw [Q_bot]
    have : x ^ 2 - 2 * x - a < 0 := by nlinarith
    nlinarith
  rw [← hx2]
  rcases lt_or_ge (x ^ 2) 2 with hlt | hge
  · -- 凸：頂点が 2x より右なので G(L) ≥ G(2x)
    have hv := vertex_right ha0 hx1 hlt (by rw [hx2]; exact hΔ)
    have hdiff := Q_sub_Q_top a L x
    have hb : 0 ≤ 4 * a - (2 - x ^ 2) * (L + 2 * x) := by
      have : (2 - x ^ 2) * (L + 2 * x) ≤ (2 - x ^ 2) * (4 * x) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have : 0 ≤ (2 * x - L) * (4 * a - (2 - x ^ 2) * (L + 2 * x)) :=
      mul_nonneg (by linarith) hb
    linarith
  · -- 凹：端の値の補間より上
    rw [Q_interp a L x hx0.ne']
    have h1 : 0 ≤ (2 - x ^ 2) * (L ^ 2 - 4 * x ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
    have h2 : 0 < (Q a (2 * x) (x ^ 2) * (L + 2 * x) + Q a (-(2 * x)) (x ^ 2) * (2 * x - L))
        / (4 * x) := by
      apply div_pos _ (by positivity)
      rcases lt_or_ge L (2 * x) with hl | hl
      · have := mul_pos hbot (show 0 < 2 * x - L by linarith)
        have := mul_nonneg htop.le (show 0 ≤ L + 2 * x by linarith)
        linarith
      · have := mul_pos htop (show 0 < L + 2 * x by linarith)
        have := mul_nonneg hbot.le (show 0 ≤ 2 * x - L by linarith)
        linarith
    linarith

/-- (2) の系：地平面の外で r₀ < r_mb なら、どの L でも r₀ は遠くから来た粒子の折り返しの点でない。 -/
theorem not_turning {a L r₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hH : rH a < r₀)
    (hmb : r₀ < rmb a) : ¬ IsTurning a L r₀ := by
  intro ht
  have := no_turning_point ha0 ha1 hH hmb (outer_root_le ht)
  rw [ht.1] at this
  exact lt_irrefl _ this

/-- a < 1 なら地平面は r_mb より内側（a = 1 では一致）。 -/
theorem rH_lt_rmb {a : ℝ} (ha1 : a < 1) : rH a < rmb a := by
  unfold rH rmb
  have hs : 0 < √(1 - a) := sqrt_pos.mpr (by linarith)
  have hs2 := sq_sqrt (show 0 ≤ 1 - a by linarith)
  have hm : √(1 - a ^ 2) = √(1 - a) * √(1 + a) := by
    rw [← sqrt_mul (by linarith)]; congr 1; ring
  have h2 : √(1 + a) < 2 := by rw [sqrt_lt' (by norm_num)]; linarith
  rw [hm]
  nlinarith

theorem rH_one : rH 1 = 1 ∧ rmb 1 = 1 := by
  unfold rH rmb; norm_num

/-- (3) a < 1、r₀ = r_mb なら、折り返せる L は L² = 4r₀ だけ（二重根）。 -/
theorem rmb_double_root {a L : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hQ : Q a L (rmb a) = 0)
    (hL : L ^ 2 ≤ 4 * rmb a) : L ^ 2 = 4 * rmb a ∧ (4 * rmb a - L ^ 2 = 0) := by
  have hH := rH_lt_rmb ha1
  obtain ⟨hΔ, hr1⟩ := outside_horizon ha0 ha1.le hH
  set s := √(1 - a) with hs_def
  have hs0 : 0 < s := sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - a := sq_sqrt (by linarith)
  set x := 1 + s with hx_def
  have hx2 : x ^ 2 = rmb a := by rw [rmb_eq ha1.le]
  have hx1 : 1 < x := by simp only [hx_def]; linarith
  rw [← hx2] at hQ hL hΔ ⊢
  have htop : Q a (2 * x) (x ^ 2) = 0 := by
    rw [Q_top]; have : x ^ 2 - 2 * x + a = 0 := by simp only [hx_def]; nlinarith
    rw [this]; ring
  have hbot : 0 ≤ Q a (-(2 * x)) (x ^ 2) := by
    rw [Q_bot]
    have : x ^ 2 - 2 * x - a ≤ 0 := by simp only [hx_def]; nlinarith
    nlinarith
  have hmain : L ^ 2 = 4 * x ^ 2 := by
    by_contra hne
    have hlt : L ^ 2 < 4 * x ^ 2 := lt_of_le_of_ne hL hne
    have hLx : |L| < 2 * x := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 * x)]
      exact sq_lt_sq.mp (by nlinarith)
    have hL1 := (abs_lt.mp hLx).1
    have hL2 := (abs_lt.mp hLx).2
    rcases lt_or_ge (x ^ 2) 2 with hlt2 | hge2
    · have hv := vertex_right ha0 hx1 hlt2 hΔ
      have hdiff := Q_sub_Q_top a L x
      rw [hQ, htop] at hdiff
      have hb : 0 < 4 * a - (2 - x ^ 2) * (L + 2 * x) := by
        have : (2 - x ^ 2) * (L + 2 * x) ≤ (2 - x ^ 2) * (4 * x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith
      have : 0 < (2 * x - L) * (4 * a - (2 - x ^ 2) * (L + 2 * x)) :=
        mul_pos (by linarith) hb
      linarith
    · have hi := Q_interp a L x (by linarith)
      rw [hQ, htop, zero_mul, zero_add] at hi
      have h1 : 0 ≤ (2 - x ^ 2) * (L ^ 2 - 4 * x ^ 2) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      have h2 : 0 ≤ Q a (-(2 * x)) (x ^ 2) * (2 * x - L) / (4 * x) :=
        div_nonneg (mul_nonneg hbot (by linarith)) (by linarith)
      -- 和が 0 なので両方 0
      have h3 : Q a (-(2 * x)) (x ^ 2) * (2 * x - L) / (4 * x) = 0 := by linarith
      have h4 : (2 - x ^ 2) * (L ^ 2 - 4 * x ^ 2) = 0 := by linarith
      have hx22 : x ^ 2 = 2 := by
        rcases mul_eq_zero.mp h4 with h | h
        · linarith
        · linarith
      have hQb : Q a (-(2 * x)) (x ^ 2) = 0 := by
        rcases mul_eq_zero.mp ((div_eq_zero_iff.mp h3).resolve_right (by linarith)) with h | h
        · exact h
        · linarith
      rw [Q_bot] at hQb
      have : x ^ 2 - 2 * x - a < 0 := by nlinarith
      have : 0 < x ^ 2 + 2 * x + a := by nlinarith
      nlinarith
  rw [hmain]
  exact ⟨rfl, by ring⟩

/-- (4) r₀ > r_mb なら、0 < L、L² < 4r₀ の L で単根の折り返しの点になる。 -/
theorem turning_point_exists {a r₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (h : rmb a < r₀) :
    ∃ L, 0 < L ∧ L ^ 2 < 4 * r₀ ∧ IsTurning a L r₀ := by
  set s := √(1 - a) with hs_def
  have hs0 : 0 ≤ s := sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - a := sq_sqrt (by linarith)
  have hr0 : 0 < r₀ := by
    have := rmb_eq ha1; have : 0 < rmb a := by rw [this]; positivity
    linarith
  set x := √r₀ with hx_def
  have hx2 : x ^ 2 = r₀ := sq_sqrt hr0.le
  have hx0 : 0 < x := sqrt_pos.mpr hr0
  have hxs : 1 + s < x := by
    rw [rmb_eq ha1] at h
    have : (1 + s) ^ 2 < x ^ 2 := by rw [hx2]; exact h
    nlinarith
  have htop : Q a (2 * x) r₀ < 0 := by
    rw [← hx2, Q_top]
    have : 0 < x ^ 2 - 2 * x + a := by nlinarith
    have : 0 < x ^ 2 + 2 * x - a := by nlinarith
    nlinarith
  have hzero : 0 < Q a 0 r₀ := by
    have : Q a 0 r₀ = 2 * r₀ ^ 2 + 2 * a ^ 2 := by unfold Q; ring
    rw [this]; positivity
  have hcont : ContinuousOn (fun L => Q a L r₀) (Set.Icc 0 (2 * x)) := by
    unfold Q; fun_prop
  obtain ⟨L, hLI, hLQ⟩ := intermediate_value_Ioo' (by linarith) hcont
    (show (0 : ℝ) ∈ Set.Ioo (Q a (2 * x) r₀) (Q a 0 r₀) from ⟨htop, hzero⟩)
  have hL2 : L ^ 2 < 4 * r₀ := by
    rw [← hx2]; nlinarith [hLI.1, hLI.2]
  have hLQ' : Q a L r₀ = 0 := hLQ
  refine ⟨L, hLI.1, hL2, hLQ', fun r hr => ?_⟩
  have e : Q a L r = Q a L r₀ + (r - r₀) * (2 * (r + r₀) - L ^ 2) := by unfold Q; ring
  rw [e, hLQ', zero_add]
  exact mul_pos (by linarith) (by linarith)

/-- (5) r_mb < 2 ⇔ a > 2√2 − 2。 -/
theorem rmb_lt_two_iff {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : rmb a < 2 ↔ 2 * √2 - 2 < a := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  have hs2 := sq_sqrt (show 0 ≤ 1 - a by linarith)
  have hs0 := sqrt_nonneg (1 - a)
  unfold rmb
  constructor
  · intro h
    have hlt : 2 * √(1 - a) < a := by linarith
    have : 4 * (1 - a) < a ^ 2 := by nlinarith
    -- (a + 2)² > 8 = (2√2)²
    have : (2 * √2) ^ 2 < (a + 2) ^ 2 := by nlinarith
    have := (pow_lt_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).mp this
    linarith
  · intro h
    have ha : 0 < a := by nlinarith
    have : (2 * √2) ^ 2 < (a + 2) ^ 2 :=
      (pow_lt_pow_iff_left₀ (by positivity) (by linarith) two_ne_zero).mpr (by linarith)
    have h4 : 4 * (1 - a) < a ^ 2 := by nlinarith
    have : √(1 - a) < a / 2 := by
      rw [sqrt_lt' (by linarith)]; nlinarith
    linarith

/-- (5) a = 1/2 では、地平面の外で r₀ < 2（エルゴ球）の折り返しの点は無い。 -/
theorem half_not {L r₀ : ℝ} (hH : rH (1 / 2) < r₀) (h2 : r₀ < 2) : ¬ IsTurning (1 / 2) L r₀ := by
  intro ht
  have hmb : 2 < rmb (1 / 2) := by
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with he | hl
    · unfold rmb at he
      have : √(1 - 1 / 2 : ℝ) = 1 / 4 := by linarith
      have h' := sq_sqrt (show (0 : ℝ) ≤ 1 - 1 / 2 by norm_num)
      rw [this] at h'; norm_num at h'
    · have := (rmb_lt_two_iff (by norm_num) (by norm_num)).mp hl
      have : √2 < 5 / 4 := by linarith
      have h' := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [sqrt_nonneg (2 : ℝ)]
  have := no_turning_point (L := L) (by norm_num) (by norm_num) hH (by linarith) (outer_root_le ht)
  rw [ht.1] at this
  exact lt_irrefl _ this

/-- その場の得（光子二つ）½(√(2/r) − 1)。 -/
noncomputable def gain (r : ℝ) : ℝ := (√(2 / r) - 1) / 2

/-- (6) 届く点 r > r_mb の得は、r_mb での値より真に小さい。 -/
theorem gain_reachable_lt {a r : ℝ} (ha1 : a ≤ 1) (h : rmb a < r) :
    gain r < gain (rmb a) := by
  have hpos : 0 < rmb a := by rw [rmb_eq ha1]; positivity
  unfold gain
  have : √(2 / r) < √(2 / rmb a) :=
    sqrt_lt_sqrt (div_pos two_pos (hpos.trans h)).le
      (div_lt_div_of_pos_left (by norm_num) hpos h)
  linarith

/-- (6) a < 1 なら r_mb での得は、地平面での得より真に小さい。 -/
theorem gain_rmb_lt_rH {a : ℝ} (ha1 : a < 1) : gain (rmb a) < gain (rH a) := by
  have hH := rH_lt_rmb ha1
  have hpos : 0 < rH a := by unfold rH; positivity
  unfold gain
  have : √(2 / rmb a) < √(2 / rH a) :=
    sqrt_lt_sqrt (div_pos two_pos (hpos.trans hH)).le
      (div_lt_div_of_pos_left (by norm_num) hpos hH)
  linarith

end Paper939

end Yamagishi
