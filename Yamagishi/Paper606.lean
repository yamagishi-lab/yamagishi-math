/-
論文606『消せる型は四つに一つ』の格上げ（一般の形）。

原稿（606_yamagishi_only_one_pattern_in_four_can_be_switched_off/…_jp.tex）は、5×5 のライツアウト
（ますを押すとそのますと上下左右が反転する。二を法とする足し算）で、掃き出しの階数 23 と 2^25 通りの
総当たりを突き合わせ、「何も変えない押し方と偶数個ずつ重なる型」が消せる型と一つ残らず一致すること
（観察 4.3）、全部点いた型が消せること（観察 4.4）を数え上げで確かめ、1〜20 の盤で核の次元を表に
している。理由としては、押す関係の対称性から「奇数個重なる型は作れない」側だけを述べている。

ここで証明した言明：
  (1) `mem_range_iff`：任意の体の上の対称な行列 M で、v が M の像に入る ⇔ M の核のすべての x と
      x·v = 0（像 = 核の直交補。両向き）。
  (2) `card_range`：二を法とする場合、作れる型の数は 2^(n − dim ker M)、すなわち全体の
      1/2^(dim ker M)（`card_range_mul`）。
  (3) `all_on_solvable`（Sutner の定理）：どの有限のグラフでも、押し方の行列 M = 隣接行列 + I
      （二を法）で、全部点いた型は必ず消せる。
定義に置いたもの：ライツアウトの盤を一般のグラフに置き換え、押すことを M = 隣接行列 + I を掛けること
とした（盤の上下左右の隣をつなぐグラフが原稿の盤）。
既知との関係：(1) は線形代数の教科書の事実、(3) は Sutner（1989）の定理そのもの。Mathlib には
ライツアウトの定理は無く、双対の消える部分の一般の事実（`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`）
から導いた。
形式化していないもの：5×5 で核の次元が 2 であること、1〜20 の盤の次元の表（具体的な掃き出し）。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper606

open Matrix

set_option linter.unusedSectionVars false

section Field

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 対称な行列で、x·(M y) = (M x)·y。 -/
theorem dot_mulVec_symm {M : Matrix ι ι K} (hM : Mᵀ = M) (x y : ι → K) :
    x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM]

/-- (1) 対称な行列の像は、核の直交補にちょうど等しい。 -/
theorem mem_range_iff {M : Matrix ι ι K} (hM : Mᵀ = M) (v : ι → K) :
    (∃ y, M *ᵥ y = v) ↔ ∀ x, M *ᵥ x = 0 → x ⬝ᵥ v = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ x hx
    rw [dot_mulVec_symm hM, hx, zero_dotProduct]
  · intro h
    set W := LinearMap.range M.mulVecLin
    have key := (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W v).mp
    have : v ∈ W := by
      apply key
      intro φ hφ
      rw [Submodule.mem_dualAnnihilator] at hφ
      set x : ι → K := fun i => φ (Pi.single i 1) with hx
      have hφx : ∀ w, φ w = x ⬝ᵥ w := by
        intro w
        rw [LinearMap.pi_apply_eq_sum_univ φ w, dotProduct]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_eq_mul, mul_comm, hx]
        congr 2
        ext j; simp [Pi.single_apply, eq_comm]
      have hker : M *ᵥ x = 0 := by
        ext k
        have h0 : φ (M *ᵥ Pi.single k 1) = 0 :=
          hφ _ ⟨Pi.single k 1, rfl⟩
        rw [hφx, dot_mulVec_symm hM, dotProduct_single_one] at h0
        simpa using h0
      rw [hφx]
      exact h x hker
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩

end Field

section Two

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- (2) 二を法とする場合、作れる型の数は 2^(n − dim ker M)。 -/
theorem card_range (M : Matrix ι ι (ZMod 2)) :
    Nat.card (LinearMap.range M.mulVecLin) =
      2 ^ (Fintype.card ι - Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin)) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  omega

/-- 作れる型の割合は 1/2^(dim ker M)：（作れる型の数）× 2^(dim ker M) = 2^n。 -/
theorem card_range_mul (M : Matrix ι ι (ZMod 2)) :
    Nat.card (LinearMap.range M.mulVecLin) *
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = 2 ^ Fintype.card ι := by
  rw [card_range, ← pow_add]
  congr 1
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  omega

/-- 二を法として、対称な行列の二次形式は対角だけが残る。 -/
theorem quad_eq_diag {M : Matrix ι ι (ZMod 2)} (hM : Mᵀ = M) (x : ι → ZMod 2) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, x i * M i i * x i := by
  have e : x ⬝ᵥ (M *ᵥ x) = ∑ p ∈ Finset.univ ×ˢ Finset.univ, x p.1 * M p.1 p.2 * x p.2 := by
    rw [Finset.sum_product]
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hoff : ∑ p ∈ (Finset.univ : Finset ι).offDiag, x p.1 * M p.1 p.2 * x p.2 = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      have : M p.2 p.1 = M p.1 p.2 := by
        have := congrFun (congrFun hM p.1) p.2
        simpa using this
      simp only [Prod.fst_swap, Prod.snd_swap, this]
      rw [show x p.2 * M p.1 p.2 * x p.1 = x p.1 * M p.1 p.2 * x p.2 by ring]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      rw [Finset.mem_offDiag] at hp
      exact hp.2.2 (by simpa [Prod.ext_iff, eq_comm] using h)
    · intro p hp
      rw [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, fun h => hp.2.2 h.symm⟩
    · intro p _; exact Prod.swap_swap p
  rw [hoff, add_zero]
  rw [Finset.diag, Finset.sum_map]
  rfl

/-- (3) Sutner の定理：どの有限のグラフでも、M = 隣接行列 + I（二を法）で、全部点いた型は消せる。 -/
theorem all_on_solvable (G : SimpleGraph ι) [DecidableRel G.Adj] :
    ∃ y, (G.adjMatrix (ZMod 2) + 1) *ᵥ y = fun _ => 1 := by
  set M := G.adjMatrix (ZMod 2) + 1
  have hM : Mᵀ = M := by
    simp only [M, transpose_add, transpose_one, SimpleGraph.transpose_adjMatrix]
  have hdiag : ∀ i, M i i = 1 := by
    intro i; simp [M]
  rw [mem_range_iff hM]
  intro x hx
  have h0 : x ⬝ᵥ (M *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
  rw [quad_eq_diag hM] at h0
  have hsq : ∀ i, x i * M i i * x i = x i := by
    intro i
    rw [hdiag, mul_one]
    have : ∀ a : ZMod 2, a * a = a := by decide
    exact this (x i)
  simp only [hsq] at h0
  simpa [dotProduct] using h0

end Two

end Paper606

end Yamagishi
