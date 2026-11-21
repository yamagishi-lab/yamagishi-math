/-
論文1064『曲率を消すか、捩率を消すか』の格上げ（芯だけ：(i) の線形代数）。

原稿（1064_yamagishi_annihilate_the_curvature_or_the_torsion/…_jp.tex）は、目盛り（四脚場）e から
計量 g = eᵀηe への写像の微分の階数を、次元 2〜5 で数値で数え（3・6・10・15、届かない数 1・3・6・10）、
「届く数は対称な行列の成分数 d(d+1)/2、届かない数は反対称な行列の成分数 d(d−1)/2」と述べ、
球面と重い天体のまわりの計量で二つの接続（ヴァイツェンベック・レヴィ＝チビタ）を記号計算している。

ここで証明した言明（芯だけ。任意の次元 d、η は対称で正則、e は正則）：
  計量への写像 e ↦ eᵀηe の e での微分 D(δ) = eᵀηδ + δᵀηe について
  (1) `D_symm`：D(δ) はいつも対称。
  (2) `D_surj`：どの対称な S にも D(δ) = S となる δ が在る（δ = (eᵀη)⁻¹S/2）。
      よって D の像はちょうど対称な行列の全体（`range_D`）。
  (3) `D_ker_iff`：D(δ) = 0 ⇔ eᵀηδ が反対称。`ker_equiv`：核は反対称な行列の全体と、
      δ ↦ eᵀηδ で線形に同型（δ = eX と書けば、X が計量 g を保つ変換のリー代数に入ること）。
  よって階数 = 対称な行列の次元、核の次元 = 反対称な行列の次元（d(d+1)/2 と d(d−1)/2 という
  数そのものの数え上げは、ここでは行っていない）。
形式化していないもの：(ii) のヴァイツェンベック接続・レヴィ＝チビタ接続・捩率・曲率（Mathlib に
接続と捩率の一般の道具が無いため止めた）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1064

open Matrix

variable {d : ℕ}

/-- 計量への写像 e ↦ eᵀηe の、e での微分。 -/
def D (η e : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun δ := eᵀ * η * δ + δᵀ * η * e
  map_add' a b := by simp [Matrix.mul_add, Matrix.add_mul, transpose_add]; abel
  map_smul' r a := by simp [transpose_smul]

/-- D(δ) = A + Aᵀ（A = eᵀηδ、η は対称）。 -/
theorem D_eq {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (δ : Matrix (Fin d) (Fin d) ℝ) :
    D η e δ = eᵀ * η * δ + (eᵀ * η * δ)ᵀ := by
  show eᵀ * η * δ + δᵀ * η * e = _
  rw [transpose_mul, transpose_mul, hη, transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- (1) D(δ) はいつも対称。 -/
theorem D_symm {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (δ : Matrix (Fin d) (Fin d) ℝ) :
    (D η e δ)ᵀ = D η e δ := by
  rw [D_eq hη, transpose_add, transpose_transpose, add_comm]

/-- (2) どの対称な S にも D(δ) = S となる δ が在る。 -/
theorem D_surj {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (hηi : IsUnit η.det)
    (hei : IsUnit e.det) (S : Matrix (Fin d) (Fin d) ℝ) (hS : Sᵀ = S) :
    ∃ δ, D η e δ = S := by
  set B := eᵀ * η
  have hB : IsUnit B.det := by
    rw [det_mul, det_transpose]; exact hei.mul hηi
  refine ⟨B⁻¹ * ((1 / 2 : ℝ) • S), ?_⟩
  rw [D_eq hη]
  have : B * (B⁻¹ * ((1 / 2 : ℝ) • S)) = (1 / 2 : ℝ) • S := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.one_mul]
  rw [this, transpose_smul, hS, ← add_smul]
  norm_num

/-- D の像は、ちょうど対称な行列の全体。 -/
theorem range_D {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (hηi : IsUnit η.det)
    (hei : IsUnit e.det) (S : Matrix (Fin d) (Fin d) ℝ) :
    S ∈ LinearMap.range (D η e) ↔ Sᵀ = S := by
  constructor
  · rintro ⟨δ, rfl⟩; exact D_symm hη δ
  · intro hS; exact D_surj hη hηi hei S hS

/-- (3) D(δ) = 0 ⇔ eᵀηδ が反対称。 -/
theorem D_ker_iff {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (δ : Matrix (Fin d) (Fin d) ℝ) :
    D η e δ = 0 ↔ (eᵀ * η * δ)ᵀ = -(eᵀ * η * δ) := by
  rw [D_eq hη]
  constructor
  · intro h; exact eq_neg_of_add_eq_zero_right h
  · intro h; rw [h, add_neg_cancel]

/-- 反対称な行列の部分空間。 -/
def skew (d : ℕ) : Submodule ℝ (Matrix (Fin d) (Fin d) ℝ) where
  carrier := {A | Aᵀ = -A}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_add, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [transpose_smul, ha, smul_neg]

/-- 核は反対称な行列の全体と、δ ↦ eᵀηδ で線形に同型。 -/
noncomputable def ker_equiv {η e : Matrix (Fin d) (Fin d) ℝ} (hη : ηᵀ = η) (hηi : IsUnit η.det)
    (hei : IsUnit e.det) : LinearMap.ker (D η e) ≃ₗ[ℝ] skew d := by
  set B := eᵀ * η with hBdef
  have hB : IsUnit B.det := by
    rw [hBdef, det_mul, det_transpose]; exact hei.mul hηi
  exact
  { toFun := fun δ => ⟨B * δ.1, by
      exact (D_ker_iff (e := e) hη δ.1).mp (LinearMap.mem_ker.mp δ.2)⟩
    invFun := fun A => ⟨B⁻¹ * A.1, by
      rw [LinearMap.mem_ker, D_ker_iff hη]
      rw [← hBdef, ← Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.one_mul]
      exact A.2⟩
    map_add' := fun a b => by ext1; simp [Matrix.mul_add]
    map_smul' := fun r a => by ext1; simp
    left_inv := fun δ => by
      ext1
      simp only
      rw [← Matrix.mul_assoc, nonsing_inv_mul B hB, Matrix.one_mul]
    right_inv := fun A => by
      ext1
      simp only
      rw [← Matrix.mul_assoc, mul_nonsing_inv B hB, Matrix.one_mul] }

end Paper1064

end Yamagishi
