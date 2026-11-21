/-
論文1101『凹んだ立体は影を失うが、平均の弦は保つ』の格上げ（芯だけ）。

原稿（1101_yamagishi_a_dented_body_loses_shadow_but_keeps_the_mean_chord/…_jp.tex）は、単位立方体を
並べた六つの形と単位正方形を並べた五つの形で、運動に不変な選び方の直線 1200 万本を数え、区間ごとの
平均の長さが凸でなくても 4V/S（平面では πA/L）のまま残ること、凹むと影（当たる直線の数）が減ること
を数えている。

ここで証明した言明（芯だけ）：
  (1) `hull_avoids`：実の線形空間の超平面 {x | f x = c}（f は連続な線形汎関数）が、連結な集合 K に
      当たらなければ、K の凸包にも当たらない。平面では直線がちょうど超平面なので、
      連結な平面の形に当たる直線と、その凸包に当たる直線は一致する（`hits_iff`）。
  (2) `space_counterexample`：空間ではこれが崩れる。xy 平面の単位円（連結）に z 軸は当たらないが、
      z 軸は単位円の凸包（原点）に当たる。
形式化していないもの：クロフトンの公式と、区間ごとの平均の長さ 4V/S（Mathlib に積分幾何の道具が
無いため止めた）。当たった直線一本あたりの区間の数が 1 以上であることは、数え方からほぼ自明なので
扱わない。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper1101

open Set

section Hyperplane

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- 連結な K の上で f が c をとらなければ、K は f < c か f > c の片側に入る。 -/
theorem one_side {K : Set E} (hK : IsPreconnected K) {f : E →ₗ[ℝ] ℝ} (hf : Continuous f)
    {c : ℝ} (hmiss : ∀ x ∈ K, f x ≠ c) : (∀ x ∈ K, f x < c) ∨ (∀ x ∈ K, c < f x) := by
  by_contra h
  push Not at h
  obtain ⟨⟨a, ha, hac⟩, ⟨b, hb, hbc⟩⟩ := h
  have ha' : c < f a := lt_of_le_of_ne hac (fun e => hmiss a ha e.symm)
  have hb' : f b < c := lt_of_le_of_ne hbc (hmiss b hb)
  have := hK.intermediate_value hb ha hf.continuousOn ⟨hb'.le, ha'.le⟩
  obtain ⟨z, hz, hzc⟩ := this
  exact hmiss z hz hzc

/-- (1) 超平面が連結な K に当たらなければ、K の凸包にも当たらない。 -/
theorem hull_avoids {K : Set E} (hK : IsPreconnected K) {f : E →ₗ[ℝ] ℝ} (hf : Continuous f)
    {c : ℝ} (hmiss : ∀ x ∈ K, f x ≠ c) : ∀ x ∈ convexHull ℝ K, f x ≠ c := by
  rcases one_side hK hf hmiss with h | h
  · have hsub : convexHull ℝ K ⊆ {x | f x < c} :=
      convexHull_min (fun x hx => h x hx) (convex_halfSpace_lt f.isLinear c)
    intro x hx; exact (hsub hx).ne
  · have hsub : convexHull ℝ K ⊆ {x | c < f x} :=
      convexHull_min (fun x hx => h x hx) (convex_halfSpace_gt f.isLinear c)
    intro x hx; exact (hsub hx).ne'

/-- 連結な K に当たる超平面と、その凸包に当たる超平面は一致する。 -/
theorem hits_iff {K : Set E} (hK : IsPreconnected K) {f : E →ₗ[ℝ] ℝ} (hf : Continuous f)
    (c : ℝ) : (∃ x ∈ K, f x = c) ↔ (∃ x ∈ convexHull ℝ K, f x = c) := by
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, subset_convexHull ℝ K hx, h⟩
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨x, hx, hxc⟩ := h
    exact hull_avoids hK hf hn x hx hxc

end Hyperplane

/-! ## (2) 空間では崩れる -/

/-- xy 平面の単位円。 -/
def circle3 : Set (Fin 3 → ℝ) := {p | p 2 = 0 ∧ p 0 ^ 2 + p 1 ^ 2 = 1}

/-- z 軸。 -/
def zAxis : Set (Fin 3 → ℝ) := {p | p 0 = 0 ∧ p 1 = 0}

theorem circle3_connected : IsConnected circle3 := by
  have : circle3 = (fun t : ℝ => ![Real.cos t, Real.sin t, 0]) '' univ := by
    ext p
    simp only [circle3, mem_ofPred_eq, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨h2, h01⟩
      obtain ⟨t, ht⟩ : ∃ t, Real.cos t = p 0 ∧ Real.sin t = p 1 := by
        have hz : ‖(⟨p 0, p 1⟩ : ℂ)‖ = 1 := by
          rw [Complex.norm_def, Complex.normSq_mk]
          rw [show p 0 * p 0 + p 1 * p 1 = 1 by nlinarith]; simp
        refine ⟨Complex.arg ⟨p 0, p 1⟩, ?_, ?_⟩
        · have := Complex.cos_arg (x := ⟨p 0, p 1⟩) (by
            intro h; rw [h] at hz; simp at hz)
          rw [this, hz]; simp
        · have := Complex.sin_arg (⟨p 0, p 1⟩ : ℂ)
          rw [this, hz]; simp
      refine ⟨t, ?_⟩
      ext i; fin_cases i <;> simp [ht.1, ht.2, h2]
    · rintro ⟨t, rfl⟩
      simp [Real.cos_sq_add_sin_sq]
  rw [this]
  exact isConnected_univ.image _ (by fun_prop)

/-- z 軸は単位円に当たらないが、単位円の凸包には当たる（原点）。 -/
theorem space_counterexample :
    (zAxis ∩ circle3 = ∅) ∧ (0 : Fin 3 → ℝ) ∈ zAxis ∩ convexHull ℝ circle3 := by
  constructor
  · ext p
    simp only [zAxis, circle3, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨h0, h1⟩, _, h⟩
    rw [h0, h1] at h; norm_num at h
  · refine ⟨⟨rfl, rfl⟩, ?_⟩
    have ha : (![1, 0, 0] : Fin 3 → ℝ) ∈ circle3 := by simp [circle3]
    have hb : (![-1, 0, 0] : Fin 3 → ℝ) ∈ circle3 := by simp [circle3]
    have hc := (convex_convexHull ℝ circle3) (subset_convexHull ℝ _ ha)
      (subset_convexHull ℝ _ hb) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    convert hc using 1
    ext i; fin_cases i <;> simp

end Paper1101

end Yamagishi
