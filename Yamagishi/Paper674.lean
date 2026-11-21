/-
論文674『温度も引力も要らない相転移』の格上げ（芯だけ）。

原稿（674_yamagishi_phase_transitions_that_need_neither_temperature_nor_attraction/…_jp.tex）は、
摩擦の無い球が詰まって動けなくなる（剛になる）ときの平均の接触数を、平面 4・空間 6 と二つの値で
書いている（計算 3.3。導き方は書かれていない）。

ここで証明した言明（芯だけ・マクスウェルの数え上げの下からの評価）：
  d 次元で N 個の粒、接触の集まり κ（有限）。接触 c は粒 a(c) と、もう一つの粒 b(c) か壁
  （b(c) = none）とのあいだにあり、向き n(c) ∈ ℝ^d をもつ。摩擦の無い接触の拘束は
  「接触の向きに沿った相対の速さが 0」なので、無限小の動き v（粒ごとに ℝ^d の速度）から
  拘束の値への線形写像（剛性の写像）
    R(v)_c = n(c)·(v_{a(c)} − v_{b(c)})（壁なら n(c)·v_{a(c)}）
  を考える。
  (1) `contacts_ge`：剛（R の核が 0、すなわち拘束を満たす動きが 0 だけ）なら、接触の数 ≥ dN。
  (2) 壁が無く粒どうしの接触だけなら、全体の平行移動がいつも拘束を満たす（`translation_in_ker`）
      ので「単射」にはならない。そこで剛を「拘束を満たす動きは全体の平行移動だけ」と置くと、
      `contacts_ge_of_free`：接触の数 ≥ dN − d、`mean_contacts_ge`：平均の接触数
      z = 2·（接触の数）/N ≥ 2d − 2d/N（N → ∞ で 2d：平面で 4、空間で 6）。
仮定として置いたもの：剛を「無限小の剛性（剛性の写像が単射）」で定めた。壁が固定されていること
（壁との接触は粒の速度だけで拘束を書く）。
形式化していないもの：半径が一般の位置なら z がちょうど 2d に近づく（等静性）という等号の側
（ここが難しい所で、Mathlib に道具が無いため止めた）。摩擦のある球の d + 1。
注意（下読みの AI の指摘）：原稿は「力とモーメントが釣り合うのに要る接触数」と書くが、摩擦の無い
球では力が中心を通るのでモーメントは自動で釣り合い、2d は力だけの数え上げから出る（ここでも
速度の拘束だけを数えている）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper674

open Module

variable {d N : ℕ} {κ : Type*} [Fintype κ]

set_option linter.unusedSectionVars false

/-- 剛性の写像：無限小の動き v から、各接触の向きに沿った相対の速さへ。 -/
def rigidity (a : κ → Fin N) (b : κ → Option (Fin N)) (n : κ → Fin d → ℝ) :
    (Fin N → Fin d → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun v c := n c ⬝ᵥ (v (a c) - (match b c with | some j => v j | none => 0))
  map_add' v w := by
    ext c
    cases h : b c <;> simp [h, dotProduct_add, dotProduct_sub]; ring
  map_smul' r v := by
    ext c
    cases h : b c <;> simp [h, dotProduct_smul, dotProduct_sub, mul_sub]

/-- (1) 剛（剛性の写像が単射）なら、接触の数 ≥ dN。 -/
theorem contacts_ge (a : κ → Fin N) (b : κ → Option (Fin N)) (n : κ → Fin d → ℝ)
    (hrigid : Function.Injective (rigidity a b n)) : d * N ≤ Fintype.card κ := by
  have := LinearMap.finrank_le_finrank_of_injective hrigid
  simp only [finrank_fintype_fun_eq_card] at this
  rw [Module.finrank_pi_fintype] at this
  simpa [mul_comm] using this

/-- 壁が無ければ、全体の平行移動はいつも拘束を満たす（だから (1) の「単射」は壁のある場合の話）。 -/
theorem translation_in_ker (a : κ → Fin N) (j : κ → Fin N) (n : κ → Fin d → ℝ) (t : Fin d → ℝ) :
    rigidity a (fun c => some (j c)) n (fun _ => t) = 0 := by
  ext c; simp [rigidity]

/-- (2) 粒どうしの接触だけで、平行移動を除いて剛（拘束を満たす動きは全体の平行移動だけ）なら、
接触の数 ≥ dN − d。 -/
theorem contacts_ge_of_free (a : κ → Fin N) (j : κ → Fin N) (n : κ → Fin d → ℝ)
    (hrigid : ∀ v, rigidity a (fun c => some (j c)) n v = 0 → ∃ t : Fin d → ℝ, ∀ i, v i = t) :
    d * N - d ≤ Fintype.card κ := by
  set R := rigidity a (fun c => some (j c)) n
  -- 核は平行移動の像に入るので、次元は d 以下
  let T : (Fin d → ℝ) →ₗ[ℝ] (Fin N → Fin d → ℝ) :=
    { toFun := fun t _ => t, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker R ≤ LinearMap.range T := by
    intro v hv
    obtain ⟨t, ht⟩ := hrigid v hv
    exact ⟨t, funext fun i => (ht i).symm⟩
  have h1 : finrank ℝ (LinearMap.ker R) ≤ d := by
    have := Submodule.finrank_mono hker
    have h2 := LinearMap.finrank_range_le T
    simp only [finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  have h3 := LinearMap.finrank_range_add_finrank_ker R
  have h4 : finrank ℝ (LinearMap.range R) ≤ Fintype.card κ := by
    have := Submodule.finrank_le (LinearMap.range R)
    simpa [finrank_fintype_fun_eq_card] using this
  rw [Module.finrank_pi_fintype] at h3
  simp only [finrank_fintype_fun_eq_card, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h3
  have : N * d = d * N := mul_comm _ _
  omega

/-- 平均の接触数 z = 2·（接触の数）/N は 2d − 2d/N 以上（N → ∞ で 2d：平面で 4、空間で 6）。 -/
theorem mean_contacts_ge (hN : 0 < N) (a : κ → Fin N) (j : κ → Fin N) (n : κ → Fin d → ℝ)
    (hrigid : ∀ v, rigidity a (fun c => some (j c)) n v = 0 → ∃ t : Fin d → ℝ, ∀ i, v i = t) :
    (2 * d : ℝ) - 2 * d / N ≤ 2 * (Fintype.card κ : ℝ) / N := by
  have h := contacts_ge_of_free a j n hrigid
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdN : d ≤ d * N := Nat.le_mul_of_pos_right d hN
  have : (d * N : ℝ) - d ≤ Fintype.card κ := by
    have : ((d * N - d : ℕ) : ℝ) ≤ Fintype.card κ := by exact_mod_cast h
    rwa [Nat.cast_sub hdN, Nat.cast_mul] at this
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']
  linarith

end Paper674

end Yamagishi
