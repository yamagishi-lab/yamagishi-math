/-
論文912『温度の係数は、どの次元でも単位球の体積である』の数学の中身を、機械に確かめさせる。

原稿（912_yamagishi_temperature_coefficient_is_the_unit_ball_volume_in_every_dimension/…_jp.tex）の
  第1節：S_{d−1} = 2π^{d/2}/Γ(d/2)、V_d = π^{d/2}/Γ(d/2+1) = S_{d−1}/d。
    等分配 ⟨½mv²⟩ = (d/2)kT から kT/⟨v²⟩ = m/d、m = S_{d−1} と置けば V_d。
  第3節（本稿の芯）：単位球面で ∮ n₁² dS = V_d（発散定理の一行）、
    だから kT/⟨v²⟩ = S_{d−1}⟨n₁²⟩ = ∮ n₁² dS = V_d。
  第5節：m を 4π に固定すると係数 4π/d が V_d と一致するのは d = 3 だけ（表は d = 1〜8）。
  第6節：横向きの ∮(1 − n₁²) dS = S_{d−1} − V_d = (d − 1)V_d。

書き方：
・球面の面積の測度は Mathlib の `Measure.toSphere`（体積から作る球面の測度。全体の重さは d·V_d）を
  使い、単位球の体積は本物のルベーグ測度の値として Mathlib の `EuclideanSpace.volume_ball` から出した。
・芯の ∮ n₁² dS = V_d は、原稿の発散定理の道ではなく、対称性の道で証明した：
  球面の測度が座標の入れ替え（直交変換）で変わらないことを示し（Mathlib に無いので、ここで証明した）、
  ∮ n_i² がどの i でも同じであること、和 Σ n_i² = 1 から ∮ Σ n_i² = S_{d−1} = d·V_d、よって各 ∮ n_i² = V_d。
  Mathlib には一般の領域（球）の発散定理がまだ無いので、原稿の一行そのものは形式化していない。
  結論（等式）は同じである。
・等分配そのもの（⟨½mv²⟩ = (d/2)kT）と、速さと向きの独立（⟨v₁²⟩ = ⟨v²⟩⟨n₁²⟩）は物理の入力として置き、
  そこから先の代数を書いた。

形式化していないもの：マクスウェル分布の乱数による数表（計算 2.1・3.1・4.1）、圧力と回る球殻の
係数（物理の式の置き方）、「温度が体積ではない」「質量は面積ではない」という読み、第7節の分離子、
V_d が d = 5 で最大という事実（論文59）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper912

open Real MeasureTheory Metric
open scoped Pointwise

/-! ### 第1節：単位球の体積と球面の面積 -/

/-- d 次元の単位球の体積 V_d = π^{d/2}/Γ(d/2 + 1)（自然数 d、√π^d と書く）。 -/
noncomputable def V (d : ℕ) : ℝ := √π ^ d / Gamma (d / 2 + 1)

/-- d 次元の単位球面の面積 S_{d−1} = 2π^{d/2}/Γ(d/2)。 -/
noncomputable def S (d : ℕ) : ℝ := 2 * √π ^ d / Gamma (d / 2)

/-- V_d = S_{d−1}/d（d ≥ 1）。 -/
theorem S_eq_mul_V (d : ℕ) (hd : 1 ≤ d) : S d = d * V d := by
  have hd' : (d : ℝ) / 2 ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hG : Gamma ((d : ℝ) / 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  unfold S V
  rw [Gamma_add_one hd']
  field_simp

/-- 本物の体積：ℝ^d の単位球のルベーグ測度は V_d。 -/
theorem volume_unit_ball (d : ℕ) (hd : 0 < d) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal = V d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal]
  · rfl
  · exact div_nonneg (by positivity) (Gamma_pos_of_pos (by positivity)).le

/-- 値：V₁ = 2、V₂ = π、V₃ = 4π/3。 -/
theorem V_one : V 1 = 2 := by
  unfold V
  have : ((1 : ℕ) : ℝ) / 2 + 1 = 1 / 2 + 1 := by norm_num
  rw [this, Gamma_add_one (by norm_num), Gamma_one_half_eq]
  have : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp

theorem V_succ_succ (d : ℕ) : V (d + 2) = 2 * π / (d + 2) * V d := by
  unfold V
  have h1 : ((d + 2 : ℕ) : ℝ) / 2 + 1 = (d / 2 + 1) + 1 := by push_cast; ring
  have hne : (d : ℝ) / 2 + 1 ≠ 0 := by positivity
  rw [h1, Gamma_add_one hne, pow_add, Real.sq_sqrt pi_pos.le]
  have hG : Gamma ((d : ℝ) / 2 + 1) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  field_simp

theorem V_zero : V 0 = 1 := by simp [V]

theorem V_two : V 2 = π := by
  have h := V_succ_succ 0
  rw [V_zero] at h; norm_num at h; exact h

theorem V_three : V 3 = 4 * π / 3 := by
  have h := V_succ_succ 1
  rw [V_one] at h; norm_num at h; rw [h]; ring

/-! ### 第1節：等分配の代数 -/

/-- 等分配 ⟨½ m v²⟩ = (d/2) kT から kT/⟨v²⟩ = m/d、m = S_{d−1} と置けば V_d
（等分配そのものは物理の入力として置く）。 -/
theorem temperature_coefficient (d : ℕ) (hd : 1 ≤ d) (kT v2 : ℝ) (hv : v2 ≠ 0)
    (hequi : (1 / 2) * S d * v2 = (d / 2) * kT) : kT / v2 = V d := by
  have hd' : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  rw [S_eq_mul_V d hd] at hequi
  field_simp
  have : kT = V d * v2 := by
    have h2 : (d : ℝ) * kT = d * (V d * v2) := by linarith
    exact mul_left_cancel₀ hd' h2
  linarith

/-! ### 第3節（芯）：球面で ∮ n₁² dS = V_d -/

/-- 単位球面の上の面積の測度（Mathlib の `toSphere`）。 -/
noncomputable abbrev σ (d : ℕ) : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

/-- 球面の全体の面積は d·V_d = S_{d−1}。 -/
theorem sigma_univ (d : ℕ) (hd : 0 < d) : (σ d).real Set.univ = d * V d := by
  rw [σ, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, measureReal_def,
    volume_unit_ball d hd]

/-- 直交変換 L を球面に制限した写像。 -/
def sphereMap {d : ℕ} (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  fun ω => ⟨L ω, by simp⟩

theorem continuous_sphereMap {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Continuous (sphereMap L) :=
  Continuous.subtype_mk (L.continuous.comp continuous_subtypeVal) _

/-- 球面の測度は直交変換で変わらない（Mathlib に無いので、ここで示す）。 -/
theorem sigma_map {d : ℕ} (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (σ d).map (sphereMap L) = σ d := by
  have hm : Measurable (sphereMap L) := (continuous_sphereMap L).measurable
  ext s hs
  rw [Measure.map_apply hm hs, σ, Measure.toSphere_apply' _ (hm hs), Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereMap L ⁻¹' s)) =
      (⇑L) ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, _, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨sphereMap L ω, hω, rfl⟩, by simp [sphereMap]⟩
    · rintro ⟨r, hr, _, ⟨ω, hω, rfl⟩, hx⟩
      refine ⟨r, hr, L.symm ω, ⟨⟨L.symm ω, by simp⟩, ?_, rfl⟩, ?_⟩
      · have : sphereMap L ⟨L.symm ω, by simp⟩ = ω := by
          ext1; simp [sphereMap]
        rw [this]; exact hω
      · have := congrArg L.symm hx
        simp only [LinearIsometryEquiv.symm_apply_apply, map_smul] at this
        exact this
  rw [hset]
  exact (L.measurePreserving).measure_preimage_emb L.toHomeomorph.measurableEmbedding _

/-- 積分も直交変換で変わらない。 -/
theorem integral_comp_sphereMap {d : ℕ}
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ) (hf : Continuous f) :
    ∫ ω, f (sphereMap L ω) ∂σ d = ∫ ω, f ω ∂σ d := by
  rw [← integral_map (continuous_sphereMap L).measurable.aemeasurable
    hf.aestronglyMeasurable, sigma_map]

/-- 座標を入れ替える直交変換。 -/
noncomputable def swapL {d : ℕ} (i j : Fin d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem swapL_apply {d : ℕ} (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : swapL i j x i = x j := by
  simp [swapL, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- 球面の上の連続関数は積分できる。 -/
theorem integrable_of_continuous {d : ℕ} (f : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ)
    (hf : Continuous f) : Integrable f (σ d) :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport f) (Set.subset_univ _))

/-- ∮ n_i² は、どの向き i でも同じ。 -/
theorem coord_sq_integral_eq {d : ℕ} (i j : Fin d) :
    ∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) j) ^ 2 ∂σ d =
      ∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d := by
  have hf : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2) := by fun_prop
  rw [← integral_comp_sphereMap (swapL i j) _ hf]
  congr 1
  ext ω
  simp [sphereMap, swapL_apply]

/-- 本稿の芯：単位球面の上で ∮ n_i² dS = V_d（どの向き i でも、どの次元 d ≥ 1 でも）。 -/
theorem sphere_integral_coord_sq (d : ℕ) (i : Fin d) :
    ∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d = V d := by
  have hd : 0 < d := Fin.pos i
  have hsum : ∫ ω, ∑ j, ((ω : EuclideanSpace ℝ (Fin d)) j) ^ 2 ∂σ d = d * V d := by
    have : (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        ∑ j, ((ω : EuclideanSpace ℝ (Fin d)) j) ^ 2) = fun _ => 1 := by
      ext ω
      rw [← EuclideanSpace.real_norm_sq_eq]
      simp [norm_eq_of_mem_sphere ω]
    rw [this, integral_const, smul_eq_mul, mul_one, sigma_univ d hd]
  rw [integral_finsetSum _ (fun j _ => integrable_of_continuous _ (by fun_prop))] at hsum
  simp only [coord_sq_integral_eq i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  exact mul_left_cancel₀ hd' hsum

/-- 芯の言い換え：方向の二乗の球面平均は ⟨n_i²⟩ = 1/d。 -/
theorem mean_coord_sq (d : ℕ) (i : Fin d) :
    (∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d) / (σ d).real Set.univ = 1 / d := by
  have hd : 0 < d := Fin.pos i
  have hV : 0 < V d := by
    unfold V; exact div_pos (by positivity) (Gamma_pos_of_pos (by positivity))
  rw [sphere_integral_coord_sq, sigma_univ d hd]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- 第3節の結び：速さと向きの独立 ⟨v₁²⟩ = ⟨v²⟩⟨n₁²⟩ と等分配 kT = m⟨v₁²⟩ を入力に置き、
m = S_{d−1} なら kT/⟨v²⟩ = S_{d−1}⟨n₁²⟩ = ∮ n₁² dS = V_d。 -/
theorem temperature_is_surface_integral (d : ℕ) (i : Fin d) (kT v2 v12 : ℝ) (hv : v2 ≠ 0)
    (hindep : v12 = v2 * ((∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d) /
      (σ d).real Set.univ))
    (hequi : kT = (σ d).real Set.univ * v12) :
    kT / v2 = ∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d ∧ kT / v2 = V d := by
  have hd : 0 < d := Fin.pos i
  have hS : (σ d).real Set.univ ≠ 0 := by
    rw [sigma_univ d hd]
    have hV : 0 < V d := by
      unfold V; exact div_pos (by positivity) (Gamma_pos_of_pos (by positivity))
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have h1 : kT / v2 = ∫ ω, ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2 ∂σ d := by
    rw [hequi, hindep]
    field_simp
  exact ⟨h1, h1.trans (sphere_integral_coord_sq d i)⟩

/-! ### 第6節：横向きの平均 -/

/-- 横向き：∮ (1 − n_i²) dS = S_{d−1} − V_d = (d − 1)V_d。 -/
theorem sphere_integral_transverse (d : ℕ) (i : Fin d) :
    ∫ ω, (1 - ((ω : EuclideanSpace ℝ (Fin d)) i) ^ 2) ∂σ d = (d - 1) * V d := by
  rw [integral_sub (integrable_const 1) (integrable_of_continuous _ (by fun_prop)),
    integral_const, smul_eq_mul, mul_one, sigma_univ d (Fin.pos i), sphere_integral_coord_sq]
  ring

/-- 横向きの積分が V_d と一致するのは d = 2 だけ（d ≥ 1）。 -/
theorem transverse_eq_V_iff (d : ℕ) (hd : 1 ≤ d) : ((d : ℝ) - 1) * V d = V d ↔ d = 2 := by
  have hV : 0 < V d := by
    unfold V; exact div_pos (by positivity) (Gamma_pos_of_pos (by positivity))
  constructor
  · intro h
    have : ((d : ℝ) - 1) = 1 := by
      have := mul_right_cancel₀ hV.ne' (h.trans (one_mul _).symm)
      exact this
    have : (d : ℝ) = 2 := by linarith
    exact_mod_cast this
  · rintro rfl; norm_num

/-! ### 第5節：m を 4π に固定すると -/

/-- m = 4π を固定したとき、係数 4π/d が V_d と一致するのは、d = 1〜8 のうち d = 3 だけ
（原稿の計算 5.1 の表の範囲。π の大小 3.14 < π < 3.15 だけを使う）。 -/
theorem fixed_four_pi_table :
    4 * π / 3 = V 3 ∧ 4 * π / 1 ≠ V 1 ∧ 4 * π / 2 ≠ V 2 ∧ 4 * π / 4 ≠ V 4 ∧
    4 * π / 5 ≠ V 5 ∧ 4 * π / 6 ≠ V 6 ∧ 4 * π / 7 ≠ V 7 ∧ 4 * π / 8 ≠ V 8 := by
  have V4 : V 4 = π ^ 2 / 2 := by
    have h := V_succ_succ 2; rw [V_two] at h; norm_num at h; rw [h]; field_simp; ring
  have V5 : V 5 = 8 * π ^ 2 / 15 := by
    have h := V_succ_succ 3; rw [V_three] at h; norm_num at h; rw [h]; field_simp; ring
  have V6 : V 6 = π ^ 3 / 6 := by
    have h := V_succ_succ 4; rw [V4] at h; norm_num at h; rw [h]; field_simp
  have V7 : V 7 = 16 * π ^ 3 / 105 := by
    have h := V_succ_succ 5; rw [V5] at h; norm_num at h; rw [h]; field_simp; ring
  have V8 : V 8 = π ^ 4 / 24 := by
    have h := V_succ_succ 6; rw [V6] at h; norm_num at h; rw [h]; field_simp; ring
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  refine ⟨V_three.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [V_one]; intro h; nlinarith
  · rw [V_two]; intro h; nlinarith
  · rw [V4]; intro h; nlinarith
  · rw [V5]; intro h; nlinarith
  · rw [V6]; intro h; nlinarith [sq_nonneg π]
  · rw [V7]; intro h; nlinarith [sq_nonneg π]
  · rw [V8]; intro h
    have hp : 0 < π := pi_pos
    have h3 : π ^ 3 = 12 := by field_simp at h; nlinarith [h]
    nlinarith [h3]

end Paper912

end Yamagishi
