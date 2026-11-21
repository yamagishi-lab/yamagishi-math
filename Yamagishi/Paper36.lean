/-
論文36『ストークス抵抗の 6π の π は、立体角である』の芯（格上げの一部）。

原稿（36_yamagishi_the_pi_in_stokes_drag/…_jp.tex）は、d 次元のストークス流の解を
ストークスレット G と勢位双極子 D の重ね合わせ u = U(e₁ + A G + B D)、p = CμU x₁ r^(−d) と置き、
d = 3〜7 の五つで残差 0・粘着条件（極と赤道の二点）・抵抗の係数 3/2, 8/3, 15/4, 24/5, 35/6 を
記号計算で照合して F = d(d − 2)/(d − 1)·Vol(S^(d−1))·μUa^(d−2) を立てる。一般の d の導出は無い。

ここで証明した言明（流体の方程式そのものは形式化していない。何を入力に置いたかは各項に書く）：
  (1) `noslip_iff`：粘着条件（赤道 1 + α + β = 0、極 1 + (d − 1)α + (1 − d)β = 0、α = A a^(2−d)、
      β = B a^(−d)）⇔ α = −d/(2(d − 1))、β = −(d − 2)/(2(d − 1))（実数 d ≠ 1）。
      `noslip_relation`：そのとき B a^(−d) = ((d − 2)/d)·A a^(2−d)（確かめの係の B = A(d − 2)a²/d）。
  (2) `paradox_two`：d = 2 では粘着条件の解は α = −1、β = 0 だけで、遠方の流れの係数 1 + A は 0
      （ストークスレットが減衰しないので、遠方で U に戻れない。重ね合わせの形の中での構成）。
  (3) `traction_uniform`：球面の上の応力（圧力と変形速度の縮約）は、粘着条件の関係のもとで
      f = −2(d − 2)A a^(1−d)·e₁ と、どこでも同じになる（向き n によらない）。
      入力に置いたもの：変形速度 ∂_j u_i + ∂_i u_j と圧力の、球面 x = a n の上での式
      （G と D を手で一回微分した式。微分そのものは形式化していない）と、運動量の式から決まる
      圧力の係数 C = 2(d − 2)A。
  (4) `drag_coefficient`：一様な応力 × 球面の面積で、F/(μUa^(d−2)) = d(d − 2)/(d − 1)·S_{d−1}
      （S_{d−1} は論文912 の単位球面の面積 2π^(d/2)/Γ(d/2)）。`drag_three`：d = 3 で 6π。
      `drag_two_zero`：係数は d = 2 でちょうど 0。`drag_table`：d = 4〜7 で原稿の表の値。
  (5) `stokeslet_part_integral`：確かめの係が書いた「応力の x₁ 成分 −2d(d − 2)A a^(1−d) n₁²」を
      単位球面で積分した値は、一様な応力の積分と等しい（論文912 の ∮ n₁² dS = V_d を使う）。
確かめの係の案との違い：係は「球面上の応力の x₁ 成分は −2d(d − 2)μα R^(1−d) n₁²」と書いたが、
(3) のとおり応力そのものは一様（n₁² によらない）。係の式はストークスレットと圧力の部分だけで、
双極子の部分は n₁n_i の項を打ち消して一様な項を足す。積分すると双極子の部分の寄与は 0 なので、
抵抗の値は係の式でも正しく出る（(5)）。
形式化していないもの：ストークス方程式の残差が 0 であること（∇p = μ∇²u、∇·u = 0）、外部の
ストークス問題の解の一意性、d = 2 の一般の非存在（対数のストークスレット）、π の住所の読み、分離子。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib
import Yamagishi.Paper912

namespace Yamagishi

namespace Paper36

open Real Finset MeasureTheory Metric

/-! ### (1) 粘着条件 -/

/-- (1) 赤道と極の二つの条件の解。 -/
theorem noslip_iff {d α β : ℝ} (hd : d ≠ 1) :
    (1 + α + β = 0 ∧ 1 + (d - 1) * α + (1 - d) * β = 0) ↔
      (α = -d / (2 * (d - 1)) ∧ β = -(d - 2) / (2 * (d - 1))) := by
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  constructor
  · rintro ⟨h1, h2⟩
    have hb : β = -1 - α := by linarith
    rw [hb] at h2
    have ha : α * (2 * (d - 1)) = -d := by linarith
    constructor
    · field_simp; linarith
    · rw [hb]; field_simp; linarith
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; constructor <;> first | (field_simp; done) | (field_simp; ring)

/-- (1) 粘着条件の関係 β = ((d − 2)/d)·α（d ≠ 0, 1）。 -/
theorem noslip_relation {d α β : ℝ} (hd : d ≠ 1) (hd0 : d ≠ 0)
    (h : 1 + α + β = 0 ∧ 1 + (d - 1) * α + (1 - d) * β = 0) : β = (d - 2) / d * α := by
  obtain ⟨h1, h2⟩ := (noslip_iff hd).mp h
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  rw [h1, h2]; field_simp

/-- (2) d = 2：解は α = −1、β = 0 だけ。そのとき遠方の係数 1 + A = 0（d = 2 で a^(2−d) = 1 なので α = A）。 -/
theorem paradox_two {A B a : ℝ} (ha : 0 < a) :
    (1 + A * a ^ ((2 : ℝ) - 2) + B * a ^ (-(2 : ℝ)) = 0 ∧
      1 + ((2 : ℝ) - 1) * (A * a ^ ((2 : ℝ) - 2)) + (1 - 2) * (B * a ^ (-(2 : ℝ))) = 0) ↔
      (A = -1 ∧ B = 0) := by
  have h0 : a ^ ((2 : ℝ) - 2) = 1 := by norm_num
  have hp : 0 < a ^ (-(2 : ℝ)) := rpow_pos_of_pos ha _
  rw [h0]
  constructor
  · rintro ⟨h1, h2⟩
    have hB : B * a ^ (-(2 : ℝ)) = 0 := by linarith
    rcases mul_eq_zero.mp hB with h | h
    · exact ⟨by linarith, h⟩
    · linarith
  · rintro ⟨rfl, rfl⟩; constructor <;> ring

theorem paradox_far_field {A B a : ℝ} (ha : 0 < a)
    (h : 1 + A * a ^ ((2 : ℝ) - 2) + B * a ^ (-(2 : ℝ)) = 0 ∧
      1 + ((2 : ℝ) - 1) * (A * a ^ ((2 : ℝ) - 2)) + (1 - 2) * (B * a ^ (-(2 : ℝ))) = 0) :
    1 + A = 0 := by
  have := ((paradox_two ha).mp h).1; rw [this]; ring

/-! ### (3) 球面の上の応力 -/

section traction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- クロネッカーの δ。 -/
def δ (i j : ι) : ℝ := if i = j then 1 else 0

/-- 縮約の補題：Σ_j (α δ_ij + β n_i n_j + γ δ_{i i₀} n_j + η δ_{j i₀} n_i) n_j。 -/
theorem contract (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i i₀ : ι) (α β γ η : ℝ) :
    ∑ j, (α * δ i j + β * n i * n j + γ * δ i i₀ * n j + η * δ j i₀ * n i) * n j =
      α * n i + β * n i + γ * δ i i₀ + η * n i * n i₀ := by
  have e : ∀ j, (α * δ i j + β * n i * n j + γ * δ i i₀ * n j + η * δ j i₀ * n i) * n j =
      α * (δ i j * n j) + (β * n i + γ * δ i i₀) * (n j ^ 2) + η * n i * (δ j i₀ * n j) := by
    intro j; ring
  simp only [e, sum_add_distrib, ← mul_sum, hn]
  simp [δ]
  ring

/-- 球面 x = a n の上の応力 f_i（μU = 1 で割った形）。
  s = a^(1−d)、t = a^(−d−1)。変形速度と圧力の式は入力として置く：
  ストークスレット：e^G_ij = (d − 2)s(2δ_ij n₁ − 2d n_i n_j n₁)
  双極子：e^D_ij = −d t(2δ_{i1} n_j + 2δ_{j1} n_i + 2δ_ij n₁ − 2(d + 2) n_i n_j n₁)
  圧力：p = 2(d − 2)A s n₁。 -/
noncomputable def traction (d A B s t : ℝ) (n : ι → ℝ) (i₀ i : ι) : ℝ :=
  -(2 * (d - 2) * A * s * n i₀) * n i +
    ∑ j, (A * ((d - 2) * s) * (2 * δ i j * n i₀ - 2 * d * n i * n j * n i₀) +
      B * (-d * t) * (2 * δ i i₀ * n j + 2 * δ j i₀ * n i + 2 * δ i j * n i₀
        - 2 * (d + 2) * n i * n j * n i₀)) * n j

/-- (3) 粘着条件の関係 dBt = (d − 2)As のもとで、応力は一様：f = −2(d − 2)A s e₁。 -/
theorem traction_uniform {d A B s t : ℝ} (n : ι → ℝ) (hn : ∑ j, n j ^ 2 = 1) (i₀ i : ι)
    (hrel : d * B * t = (d - 2) * A * s) :
    traction d A B s t n i₀ i = -2 * (d - 2) * A * s * δ i i₀ := by
  unfold traction
  have e : ∀ j, (A * ((d - 2) * s) * (2 * δ i j * n i₀ - 2 * d * n i * n j * n i₀) +
      B * (-d * t) * (2 * δ i i₀ * n j + 2 * δ j i₀ * n i + 2 * δ i j * n i₀
        - 2 * (d + 2) * n i * n j * n i₀)) * n j =
      ((2 * A * (d - 2) * s * n i₀ - 2 * B * d * t * n i₀) * δ i j +
        (-2 * A * (d - 2) * s * d * n i₀ + 2 * B * d * t * (d + 2) * n i₀) * n i * n j +
        (-2 * B * d * t) * δ i i₀ * n j + (-2 * B * d * t) * δ j i₀ * n i) * n j := by
    intro j; ring
  rw [sum_congr rfl (fun j _ => e j), contract n hn]
  have : B * d * t = (d - 2) * A * s := by linarith
  linear_combination (2 * d * n i₀ * n i - 2 * δ i i₀) * this

end traction

/-! ### (4) 抵抗の係数 -/

open Yamagishi.Paper912

/-- 一様な応力 f₁ = −2(d − 2)A a^(1−d)（A < 0 なので流れの向きに正）に、A = −d a^(d−2)/(2(d − 1)) を入れ、
半径 a の球面の面積 a^(d−1) S_{d−1} を掛ける。 -/
theorem drag_coefficient {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) :
    (-2 * ((d : ℝ) - 2) * (-(d : ℝ) * a ^ ((d : ℝ) - 2) / (2 * ((d : ℝ) - 1)))
        * a ^ (1 - (d : ℝ))) *
        (a ^ ((d : ℝ) - 1) * S d) =
      (d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d * a ^ ((d : ℝ) - 2) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have e : a ^ (1 - (d : ℝ)) * a ^ ((d : ℝ) - 1) = 1 := by
    rw [← rpow_add ha]; norm_num
  have h : (-2 * ((d : ℝ) - 2) * (-(d : ℝ) * a ^ ((d : ℝ) - 2) / (2 * ((d : ℝ) - 1))) *
      a ^ (1 - (d : ℝ))) * (a ^ ((d : ℝ) - 1) * S d) =
      (d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d * a ^ ((d : ℝ) - 2) *
        (a ^ (1 - (d : ℝ)) * a ^ ((d : ℝ) - 1)) := by
    field_simp
  rw [h, e, mul_one]

/-- 係数 d(d − 2)/(d − 1)·S_{d−1}。 -/
noncomputable def coeff (d : ℕ) : ℝ := (d : ℝ) * ((d : ℝ) - 2) / ((d : ℝ) - 1) * S d

theorem S_val (d : ℕ) (hd : 1 ≤ d) : S d = d * V d := S_eq_mul_V d hd

/-- (4) d = 3 で 6π。 -/
theorem drag_three : coeff 3 = 6 * π := by
  unfold coeff; rw [S_val 3 (by norm_num), V_three]; push_cast; ring

/-- (4) d = 2 で係数は 0。 -/
theorem drag_two_zero : coeff 2 = 0 := by unfold coeff; norm_num

/-- (4) 原稿の表：d = 4, 5, 6, 7 で 16π²/3、10π²、24π³/5、56π³/9。 -/
theorem drag_table :
    coeff 4 = 16 / 3 * π ^ 2 ∧ coeff 5 = 10 * π ^ 2 ∧ coeff 6 = 24 / 5 * π ^ 3 ∧
      coeff 7 = 56 / 9 * π ^ 3 := by
  have V4 : V 4 = π ^ 2 / 2 := by
    have h := V_succ_succ 2; rw [V_two] at h; norm_num at h; rw [h]; field_simp; ring
  have V5 : V 5 = 8 * π ^ 2 / 15 := by
    have h := V_succ_succ 3; rw [V_three] at h; norm_num at h; rw [h]; field_simp; ring
  have V6 : V 6 = π ^ 3 / 6 := by
    have h := V_succ_succ 4; rw [V4] at h; norm_num at h; rw [h]; field_simp
  have V7 : V 7 = 16 * π ^ 3 / 105 := by
    have h := V_succ_succ 5; rw [V5] at h; norm_num at h; rw [h]; field_simp; ring
  unfold coeff
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [S_val 4 (by norm_num), V4]; push_cast; ring
  · rw [S_val 5 (by norm_num), V5]; push_cast; ring
  · rw [S_val 6 (by norm_num), V6]; push_cast; ring
  · rw [S_val 7 (by norm_num), V7]; push_cast; ring

/-! ### (5) 係の式の積分 -/

/-- (5) 単位球面で、係の式 −2d(d − 2)A s n₁² の積分 = 一様な応力 −2(d − 2)A s の積分。 -/
theorem stokeslet_part_integral (d : ℕ) (i : Fin d) (A s : ℝ) :
    ∫ ω, (-2 * (d : ℝ) * ((d : ℝ) - 2) * A * s * ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2) ∂σ d =
      ∫ _ω, (-2 * ((d : ℝ) - 2) * A * s) ∂σ d := by
  have hd : 0 < d := Fin.pos i
  rw [integral_const_mul, sphere_integral_coord_sq, integral_const, smul_eq_mul, sigma_univ d hd]
  ring

end Paper36

end Yamagishi
