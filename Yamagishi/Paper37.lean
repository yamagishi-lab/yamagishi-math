/-
論文37『6π は 4π+2π か』の格上げ（芯だけ・一般の d）。

日本語：d 次元のストークス流で球が受ける抵抗は、粘着境界で d(d − 2)/(d − 1)、完全滑り境界で
2(d − 2)/(d − 1)（単位 S_{d−1}μUa^(d−2)）で、比はどの d でも d/2。どちらの境界でも圧力の分担は
ちょうど 1/d で、残りは粘着では接線の粘性だけ、滑りでは法線の粘性だけから来る。
English: In d-dimensional Stokes flow the drag on a sphere is d(d − 2)/(d − 1) for no-slip and
2(d − 2)/(d − 1) for perfect slip (in units of S_{d−1}μUa^(d−2)), ratio d/2; in both cases pressure
gives exactly 1/d, the rest coming only from tangential viscous stress (no-slip) or only from normal
viscous stress (slip).

原稿（37_yamagishi_is_six_pi_four_plus_two/…_jp.tex）は、3 次元の流れ関数で粘着 6 = 2 + 0 + 4、
滑り 4 = 4/3 + 8/3 + 0（πμUa 単位、圧力・法線粘性・接線粘性）を出し、d = 3〜6 の四つの値の表で
粘着 d(d − 2)/(d − 1)、滑り 2(d − 2)/(d − 1)、比 d/2 に一致すると書く。一般の d の導出は無い。

ここで証明した言明（論文36 と同じく、ストークスレットと勢位双極子の重ね合わせ
u = U(e₁ + AG + BD) を置き、球面の上の速度・変形速度・圧力の式を入力に置く。
論文36 の `traction`（応力）と論文912 の `S`・`V`・`σ` を使う）：
  (1) `traction_general`：一般の A, B で、球面の上の応力は f = 2d(dBt − (d − 2)As) n₁ n − 2dBt e₁
      （s = a^(1−d)、t = a^(−d−1)）。`tangential_eq`：接線の応力 f − (f·n)n = −2dBt(e₁ − n₁n)。
  (2) `normal_velocity`：球面の上の速度の法線成分は U n₁(1 + (d − 1)α − (d − 1)β)
      （α = Aa^(2−d)、β = Ba^(−d)）。
      `tangential_zero_iff`：d ≥ 2 で、接線の応力がどの点でも 0 ⇔ dBt = 0。
      `slip_iff`：完全滑り（法線速度 0・接線応力 0）⇔ β = 0 かつ α = −1/(d − 1)。
  (3) `traction_split`：応力の流れ向きの成分 = 圧力の部分 −2(d − 2)As n₁² + 法線粘性の部分
      2(d − 1)(dBt − (d − 2)As)n₁² + 接線粘性の部分 −2dBt(1 − n₁²)。
      `integral_pressurePart`・`integral_normalPart`・`integral_tangentialPart`：単位球面の積分。
  (4) `noslip_parts`：粘着で、圧力 (d − 2)/(d − 1)·S、法線粘性 0、接線粘性 (d − 2)·S
      （×μUa^(d−2)）、合計 d(d − 2)/(d − 1)·S。`slip_parts`：滑りで、圧力 2(d − 2)/(d(d − 1))·S、
      法線粘性 2(d − 2)/d·S、接線粘性 0、合計 2(d − 2)/(d − 1)·S。
      `pressure_share`：どちらも圧力の分担はちょうど 1/d。`drag_ratio`：比は d/2（d ≥ 3）。
  (5) `three_dim`：d = 3 で粘着 2π + 0 + 4π = 6π、滑り 4π/3 + 8π/3 + 0 = 4π（原稿の表）。
形式化していないもの（論文36 と同じ）：ストークス方程式の残差が 0 であること、G と D の微分
（変形速度の式）、圧力の係数、外部の問題の解の一意性。アインシュタイン＝ストークスの読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper36
import Yamagishi.Paper912

namespace Yamagishi

namespace Paper37

open Real Finset MeasureTheory Metric
open Yamagishi.Paper36 Yamagishi.Paper912

/-! ### (1) 一般の A, B での応力 -/

section traction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (1) 一般の A, B で、球面の上の応力 f = 2d(dBt − (d − 2)As) n_{i₀} n − 2dBt e_{i₀}。 -/
theorem traction_general {d A B s t : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ i : ι) :
    traction d A B s t n i₀ i =
      2 * d * (d * B * t - (d - 2) * A * s) * n i₀ * n i - 2 * d * B * t * δ i i₀ := by
  unfold traction
  have e : ∀ j, (A * ((d - 2) * s) * (2 * δ i j * n i₀ - 2 * d * n i * n j * n i₀) +
      B * (-d * t) * (2 * δ i i₀ * n j + 2 * δ j i₀ * n i + 2 * δ i j * n i₀
        - 2 * (d + 2) * n i * n j * n i₀)) * n j =
      ((2 * A * (d - 2) * s * n i₀ - 2 * B * d * t * n i₀) * δ i j +
        (-2 * A * (d - 2) * s * d * n i₀ + 2 * B * d * t * (d + 2) * n i₀) * n i * n j +
        (-2 * B * d * t) * δ i i₀ * n j + (-2 * B * d * t) * δ j i₀ * n i) * n j := by
    intro j; ring
  rw [sum_congr rfl (fun j _ => e j), contract n hn]
  ring

/-- f·n = n_{i₀}(2d(dBt − (d − 2)As) − 2dBt)。 -/
theorem traction_dot_n {d A B s t : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ : ι) :
    ∑ j, traction d A B s t n i₀ j * n j =
      n i₀ * (2 * d * (d * B * t - (d - 2) * A * s) - 2 * d * B * t) := by
  simp_rw [traction_general n hn]
  have e : ∀ j, (2 * d * (d * B * t - (d - 2) * A * s) * n i₀ * n j - 2 * d * B * t * δ j i₀) *
      n j = 2 * d * (d * B * t - (d - 2) * A * s) * n i₀ * n j ^ 2 -
        2 * d * B * t * (δ j i₀ * n j) := by intro j; ring
  rw [sum_congr rfl (fun j _ => e j), sum_sub_distrib, ← mul_sum, ← mul_sum, hn]
  simp [δ]
  ring

/-- 接線の応力 f − (f·n)n。 -/
noncomputable def tangential (d A B s t : ℝ) (n : ι → ℝ) (i₀ i : ι) : ℝ :=
  traction d A B s t n i₀ i - (∑ j, traction d A B s t n i₀ j * n j) * n i

/-- (1) 接線の応力 = −2dBt(e_{i₀} − n_{i₀} n)。 -/
theorem tangential_eq {d A B s t : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ i : ι) :
    tangential d A B s t n i₀ i = -2 * d * B * t * (δ i i₀ - n i₀ * n i) := by
  unfold tangential
  rw [traction_dot_n n hn, traction_general n hn]
  ring

/-! ### (2) 境界条件 -/

/-- 球面 x = an の上の速度 u/U（G と D に r = a を入れた形）。 -/
def velSphere (d α β : ℝ) (n : ι → ℝ) (i₀ i : ι) : ℝ :=
  δ i i₀ * (1 + α + β) + ((d - 2) * α - d * β) * n i * n i₀

/-- (2) 法線速度 u·n = n_{i₀}(1 + (d − 1)α − (d − 1)β)。 -/
theorem normal_velocity {d α β : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ : ι) :
    ∑ i, velSphere d α β n i₀ i * n i = n i₀ * (1 + (d - 1) * α - (d - 1) * β) := by
  unfold velSphere
  have e : ∀ i, (δ i i₀ * (1 + α + β) + ((d - 2) * α - d * β) * n i * n i₀) * n i =
      (1 + α + β) * (δ i i₀ * n i) + ((d - 2) * α - d * β) * n i₀ * n i ^ 2 := by
    intro i; ring
  rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, ← mul_sum, ← mul_sum, hn]
  simp [δ]
  ring

/-- (2) 接線の応力がどの点でも 0 ⇔ dBt = 0（向き i₀ と別の向き j がある、すなわち d ≥ 2）。 -/
theorem tangential_zero_iff {d A B s t : ℝ} (i₀ j : ι) (hj : j ≠ i₀) :
    (∀ n : ι → ℝ, ∑ k, n k ^ 2 = 1 → ∀ i, tangential d A B s t n i₀ i = 0) ↔
      d * B * t = 0 := by
  constructor
  · intro h
    have hn : ∑ k, (Pi.single j (1 : ℝ) : ι → ℝ) k ^ 2 = 1 := by
      rw [sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have := h _ hn i₀
    rw [tangential_eq _ hn] at this
    simp [δ, Ne.symm hj] at this
    have : d * B * t = 0 := by
      rcases this with h1 | h1
      · rcases h1 with h2 | h2
        · rw [h2]; ring
        · rw [h2]; ring
      · rw [h1]; ring
    exact this
  · intro h n hn i
    rw [tangential_eq n hn]
    have : -2 * d * B * t = -2 * (d * B * t) := by ring
    rw [this, h]; ring

end traction

/-- (2) 完全滑り：β = 0（接線の応力 0）と法線速度 0 ⇔ β = 0 かつ α = −1/(d − 1)。 -/
theorem slip_iff {d α β : ℝ} (hd : d ≠ 1) :
    (β = 0 ∧ 1 + (d - 1) * α - (d - 1) * β = 0) ↔ (β = 0 ∧ α = -1 / (d - 1)) := by
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h1] at h2
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h1, h2]
    field_simp
    ring

/-! ### (3) 三つの部分と単位球面の積分 -/

/-- 圧力の部分（流れ向きの成分の密度、x = n₁、As = A·s）。 -/
noncomputable def pressurePart (d As x : ℝ) : ℝ := -(2 * (d - 2) * As) * x ^ 2

/-- 法線粘性の部分。 -/
noncomputable def normalPart (d As Bt x : ℝ) : ℝ := 2 * (d - 1) * (d * Bt - (d - 2) * As) * x ^ 2

/-- 接線粘性の部分。 -/
noncomputable def tangentialPart (d Bt x : ℝ) : ℝ := -(2 * d * Bt) * (1 - x ^ 2)

section split

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (3) 応力の流れ向きの成分は三つの部分の和で、それぞれ −p n₁、(f·n + p) n₁、接線の応力の成分。 -/
theorem traction_split {d A B s t : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ : ι) :
    traction d A B s t n i₀ i₀ = pressurePart d (A * s) (n i₀) +
      normalPart d (A * s) (B * t) (n i₀) + tangentialPart d (B * t) (n i₀) ∧
    -(2 * (d - 2) * A * s * n i₀) * n i₀ = pressurePart d (A * s) (n i₀) ∧
    ((∑ j, traction d A B s t n i₀ j * n j) + 2 * (d - 2) * A * s * n i₀) * n i₀ =
      normalPart d (A * s) (B * t) (n i₀) ∧
    tangential d A B s t n i₀ i₀ = tangentialPart d (B * t) (n i₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [traction_general n hn]
    unfold pressurePart normalPart tangentialPart
    simp [δ]
    ring
  · unfold pressurePart; ring
  · rw [traction_dot_n n hn]; unfold normalPart; ring
  · rw [tangential_eq n hn]; unfold tangentialPart; simp [δ]; ring

end split

theorem integral_pressurePart (d : ℕ) (i : Fin d) (As : ℝ) :
    ∫ ω, pressurePart d As ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
      -(2 * ((d : ℝ) - 2) * As) * V d := by
  unfold pressurePart
  rw [integral_const_mul, sphere_integral_coord_sq]

theorem integral_normalPart (d : ℕ) (i : Fin d) (As Bt : ℝ) :
    ∫ ω, normalPart d As Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
      2 * ((d : ℝ) - 1) * (d * Bt - (d - 2) * As) * V d := by
  unfold normalPart
  rw [integral_const_mul, sphere_integral_coord_sq]

theorem integral_tangentialPart (d : ℕ) (i : Fin d) (Bt : ℝ) :
    ∫ ω, tangentialPart d Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
      -(2 * (d : ℝ) * Bt) * (((d : ℝ) - 1) * V d) := by
  unfold tangentialPart
  rw [integral_const_mul, sphere_integral_transverse]

/-! ### (4) 粘着と滑りの内訳 -/

/-- 半径 a の球：a^(d−1)·(c/a) = c·a^(d−2)（d ≥ 2）。 -/
theorem radius_factor {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    a ^ (d - 1) * (c / a) = c * a ^ (d - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, pow_succ]
  field_simp

/-- (4) 粘着（α = −d/(2(d − 1))、β = −(d − 2)/(2(d − 1))、As = α/a、Bt = β/a）の三つの部分と合計
（単位 μU、半径 a の球面の面積 a^(d−1) を掛けた値）。 -/
theorem noslip_parts (d : ℕ) (hd : 2 ≤ d) (i : Fin d) {a : ℝ} (ha : 0 < a) :
    let As := -(d : ℝ) / (2 * ((d : ℝ) - 1)) / a
    let Bt := -((d : ℝ) - 2) / (2 * ((d : ℝ) - 1)) / a
    a ^ (d - 1) * ∫ ω, pressurePart d As ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
        ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d * a ^ (d - 2) ∧
    a ^ (d - 1) * ∫ ω, normalPart d As Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d = 0 ∧
    a ^ (d - 1) * ∫ ω, tangentialPart d Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
        ((d : ℝ) - 2) * S d * a ^ (d - 2) := by
  intro As Bt
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hS : S d = d * V d := S_eq_mul_V d (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_pressurePart, hS]
    rw [show -(2 * ((d : ℝ) - 2) * As) * V d =
      ((d : ℝ) - 2) / ((d : ℝ) - 1) * (d * V d) / a by simp only [As]; field_simp]
    rw [radius_factor hd ha]
  · rw [integral_normalPart]
    have : (d : ℝ) * Bt - (d - 2) * As = 0 := by simp only [As, Bt]; field_simp; ring
    rw [this]; ring
  · rw [integral_tangentialPart, hS]
    rw [show -(2 * (d : ℝ) * Bt) * (((d : ℝ) - 1) * V d) =
      ((d : ℝ) - 2) * (d * V d) / a by simp only [Bt]; field_simp]
    rw [radius_factor hd ha]

/-- (4) 滑り（α = −1/(d − 1)、β = 0）の三つの部分。 -/
theorem slip_parts (d : ℕ) (hd : 2 ≤ d) (i : Fin d) {a : ℝ} (ha : 0 < a) :
    let As := -1 / ((d : ℝ) - 1) / a
    let Bt := (0 : ℝ)
    a ^ (d - 1) * ∫ ω, pressurePart d As ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
        2 * ((d : ℝ) - 2) / ((d : ℝ) * ((d : ℝ) - 1)) * S d * a ^ (d - 2) ∧
    a ^ (d - 1) * ∫ ω, normalPart d As Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d =
        2 * ((d : ℝ) - 2) / d * S d * a ^ (d - 2) ∧
    a ^ (d - 1) * ∫ ω, tangentialPart d Bt ((ω : EuclideanSpace ℝ (Fin d)) i) ∂σ d = 0 := by
  intro As Bt
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hS : S d = d * V d := S_eq_mul_V d (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_pressurePart, hS]
    rw [show -(2 * ((d : ℝ) - 2) * As) * V d =
      2 * ((d : ℝ) - 2) / ((d : ℝ) * ((d : ℝ) - 1)) * (d * V d) / a by
        simp only [As]; field_simp]
    rw [radius_factor hd ha]
  · rw [integral_normalPart, hS]
    rw [show 2 * ((d : ℝ) - 1) * (d * Bt - (d - 2) * As) * V d =
      2 * ((d : ℝ) - 2) / d * (d * V d) / a by simp only [As, Bt]; field_simp; ring]
    rw [radius_factor hd ha]
  · rw [integral_tangentialPart]; simp [Bt]

/-- (4) 合計：粘着 d(d − 2)/(d − 1)·S、滑り 2(d − 2)/(d − 1)·S（×μUa^(d−2)）。 -/
theorem totals (d : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d + 0 + ((d : ℝ) - 2) * S d =
        (d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d ∧
    2 * ((d : ℝ) - 2) / ((d : ℝ) * ((d : ℝ) - 1)) * S d + 2 * ((d : ℝ) - 2) / d * S d + 0 =
        2 * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  constructor
  · field_simp; ring
  · field_simp; ring

/-- (4) どちらの境界でも、圧力の分担はちょうど 1/d（d ≥ 3）。 -/
theorem pressure_share (d : ℕ) (hd : 3 ≤ d) (hS : 0 < S d) :
    ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d / ((d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d) =
        1 / d ∧
    2 * ((d : ℝ) - 2) / ((d : ℝ) * ((d : ℝ) - 1)) * S d /
        (2 * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d) = 1 / d := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hS0 : S d ≠ 0 := hS.ne'
  constructor
  · field_simp
  · field_simp

/-- (4) 比 粘着/滑り = d/2（d ≥ 3）。 -/
theorem drag_ratio (d : ℕ) (hd : 3 ≤ d) (hS : 0 < S d) :
    (d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d / (2 * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d) =
      d / 2 := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hS0 : S d ≠ 0 := hS.ne'
  field_simp

/-- (5) d = 3（S = 4π）：粘着 2π + 0 + 4π = 6π、滑り 4π/3 + 8π/3 + 0 = 4π。 -/
theorem three_dim :
    ((3 : ℝ) - 2) / ((3 : ℝ) - 1) * S 3 = 2 * π ∧ ((3 : ℝ) - 2) * S 3 = 4 * π ∧
    2 * ((3 : ℝ) - 2) / ((3 : ℝ) * ((3 : ℝ) - 1)) * S 3 = 4 / 3 * π ∧
    2 * ((3 : ℝ) - 2) / 3 * S 3 = 8 / 3 * π ∧
    (3 : ℝ) * ((3 : ℝ) - 2) / ((3 : ℝ) - 1) * S 3 = 6 * π ∧
    2 * ((3 : ℝ) - 2) / ((3 : ℝ) - 1) * S 3 = 4 * π := by
  have h : S 3 = 4 * π := by
    rw [S_eq_mul_V 3 (by norm_num), V_three]; push_cast; ring
  rw [h]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

end Paper37

end Yamagishi
