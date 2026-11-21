/-
論文970『同じ協同の結合でも、二つ目を外れにくくして作ると、付きやすくして作るより遅く落ち着く』の格上げ（一般の形）。

原稿（970_yamagishi_same_cooperative_binding_settles_slower_when_built_by_harder_loss/…_jp.tex）は、
部位が二つの分子の三状態（結合の数 0・1・2）の速さの行列で、助け合い c を
「外れにくさ」（1→2 が x、2→1 が 2/c）と「付きやすさ」（1→2 が cx、2→1 が 2）で作り、
c = 1, 10, 100, 10000 の半分結合の濃度 x = 1/√c だけで、二つの固有値の比が √c と一致することを
数値で示している。

ここで証明した言明（速さはすべて正、c > 0, x > 0）：
  (1) `det_char`：三状態の出生死滅の速さの行列 Q（0→1 が a、1→0 が b、1→2 が e、2→1 が f）について
      det(Q − λI) = −λ(λ² + Sλ + P)、S = a + b + e + f、P = ae + af + bf。
      したがって Q の固有値は 0 と、λ² + Sλ + P = 0 の二つの根。
  (2) `same_equilibrium`：二つの作り方は同じ釣り合いの分布 (1, 2x, cx²)（の定数倍）をもつ。
  (3) `prod_ratio`：零でない二つの固有値の積の比（付きやすさ ÷ 外れにくさ）はどの x でもちょうど c。
  (4) `sum_ratio_iff`：二つの固有値の和の比が √c になる ⇔ c = 1 または c = 4 または x = 1/√c。
      `eigen_scale_iff`：二つの固有値がそろってちょうど √c 倍になる（λ が外れにくさの根 ⇔ √c·λ が
      付きやすさの根、がすべての λ で成り立つ）⇔ c = 1 または c = 4 または x = 1/√c。
      とくに c = 4 では濃度によらず 2 倍、c ≠ 1, 4 では半分結合の濃度のときだけ。
足した仮定：時間の単位と濃度の単位は原稿どおり（一つ目が外れる速さを 1）。
形式化していないもの：90 パーセントに届く時間、ヒル係数、数表の値、部位が三つ以上の場合、分離子の読み。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper970

open Matrix Real

/-- 三状態 0 ↔ 1 ↔ 2 の速さの行列（行の和が 0）。 -/
def Q (a b e f : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-a, a, 0; b, -(b + e), e; 0, f, -f]

/-- (1) det(Q − λI) = −λ(λ² + Sλ + P)。 -/
theorem det_char (a b e f l : ℝ) :
    (Q a b e f - l • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      -l * (l ^ 2 + (a + b + e + f) * l + (a * e + a * f + b * f)) := by
  rw [det_fin_three]
  simp [Q]
  ring

/-- 外れにくさで作る：1→2 が x、2→1 が 2/c。 -/
noncomputable def Qhard (c x : ℝ) := Q (2 * x) 1 x (2 / c)
/-- 付きやすさで作る：1→2 が cx、2→1 が 2。 -/
def Qeasy (c x : ℝ) := Q (2 * x) 1 (c * x) 2

/-- (2) 二つの作り方は同じ釣り合いの分布 (1, 2x, cx²) をもつ（π Q = 0）。 -/
theorem same_equilibrium {c x : ℝ} (hc : c ≠ 0) :
    vecMul ![1, 2 * x, c * x ^ 2] (Qhard c x) = 0 ∧
        vecMul ![1, 2 * x, c * x ^ 2] (Qeasy c x) = 0 := by
  constructor
  · ext j; fin_cases j <;>
      simp [Qhard, Q, vecMul, dotProduct, Fin.sum_univ_three] <;> field_simp <;> ring
  · ext j; fin_cases j <;> simp [Qeasy, Q, vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- 二つの作り方の S と P。 -/
noncomputable def Sh (c x : ℝ) : ℝ := 2 * x + 1 + x + 2 / c
noncomputable def Ph (c x : ℝ) : ℝ := 2 * x * x + 2 * x * (2 / c) + 1 * (2 / c)
def Se (c x : ℝ) : ℝ := 2 * x + 1 + c * x + 2
def Pe (c x : ℝ) : ℝ := 2 * x * (c * x) + 2 * x * 2 + 1 * 2

/-- (3) 積の比はどの x でも c。 -/
theorem prod_ratio {c : ℝ} (hc : c ≠ 0) (x : ℝ) : Pe c x = c * Ph c x := by
  unfold Pe Ph; field_simp

/-- (4) 和の比が √c ⇔ c = 1 または c = 4 または x = 1/√c。 -/
theorem sum_ratio_iff {c x : ℝ} (hc : 0 < c) :
    Se c x = √c * Sh c x ↔ c = 1 ∨ c = 4 ∨ x = 1 / √c := by
  set s := √c with hs
  have hs0 : 0 < s := sqrt_pos.mpr hc
  have hc' : c = s ^ 2 := (sq_sqrt hc.le).symm
  -- Se − s·Sh = (s − 1)(s − 2)(x − 1/s)·s … を s で整理
  have key : Se c x - s * Sh c x = (s - 1) * (s - 2) * (s * x - 1) / s := by
    unfold Se Sh; rw [hc']; field_simp; ring
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left (ne_of_gt hs0)]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; rw [hc']; have : s = 1 := by linarith
        rw [this]; norm_num
      · right; left; rw [hc']; have : s = 2 := by linarith
        rw [this]; norm_num
    · right; right; field_simp; linarith
  · rintro (h | h | h)
    · have : s = 1 := by rw [hs, h, sqrt_one]
      rw [this]; ring
    · have : s = 2 := by
        rw [hs, h, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
      rw [this]; ring
    · rw [h]; field_simp; ring

/-- 固有値（の符号を変えた速さ）は μ² − Sμ + P = 0 の根。ここでは λ² + Sλ + P = 0 の根 λ で書く。 -/
def IsRoot (S P l : ℝ) : Prop := l ^ 2 + S * l + P = 0

/-- (4) 二つの固有値がそろって √c 倍 ⇔ c = 1 または c = 4 または x = 1/√c。 -/
theorem eigen_scale_iff {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∀ l, IsRoot (Sh c x) (Ph c x) l ↔ IsRoot (Se c x) (Pe c x) (√c * l)) ↔
      c = 1 ∨ c = 4 ∨ x = 1 / √c := by
  rw [← sum_ratio_iff hc]
  set s := √c with hs
  have hs0 : 0 < s := sqrt_pos.mpr hc
  have hc' : c = s ^ 2 := (sq_sqrt hc.le).symm
  have hP : Pe c x = s ^ 2 * Ph c x := by rw [prod_ratio (ne_of_gt hc), hc']
  -- (s l)² + Se (s l) + Pe − s²(l² + Sh l + Ph) = s l (Se − s Sh)
  have key : ∀ l, (s * l) ^ 2 + Se c x * (s * l) + Pe c x - s ^ 2 * (l ^ 2 + Sh c x * l + Ph c x) =
      s * l * (Se c x - s * Sh c x) := by intro l; rw [hP]; ring
  constructor
  · intro H
    -- 外れにくさの根を一つとる：判別式は正
    have hPh : 0 < Ph c x := by unfold Ph; positivity
    have hSh : 0 < Sh c x := by unfold Sh; positivity
    by_contra hne
    have hd : Se c x - s * Sh c x ≠ 0 := sub_ne_zero.mpr hne
    -- 判別式 Sh² − 4Ph > 0
    have hdisc : 0 < Sh c x ^ 2 - 4 * Ph c x := by
      unfold Sh Ph
      have : (2 * x + 1 + x + 2 / c) ^ 2 - 4 * (2 * x * x + 2 * x * (2 / c) + 1 * (2 / c)) =
          (x + 1 - 2 / c) ^ 2 + 4 * x := by ring
      rw [this]; positivity
    set l := (-Sh c x + √(Sh c x ^ 2 - 4 * Ph c x)) / 2
    have hroot : IsRoot (Sh c x) (Ph c x) l := by
      unfold IsRoot
      have := sq_sqrt hdisc.le
      simp only [l]; nlinarith [this]
    have hl : l ≠ 0 := by
      intro h0
      have := hroot; unfold IsRoot at this; rw [h0] at this; linarith
    have := (H l).mp hroot
    unfold IsRoot at this hroot
    have e := key l
    rw [this, hroot, mul_zero, sub_zero, zero_eq_mul] at e
    rcases e with e | e
    · rcases mul_eq_zero.mp e with e | e
      · linarith
      · exact hl e
    · exact hd e
  · intro h l
    have e := key l
    rw [sub_eq_zero.mpr h, mul_zero] at e
    unfold IsRoot
    constructor
    · intro hr; rw [hr, mul_zero, sub_zero] at e; exact e
    · intro hr
      rw [hr, zero_sub, neg_eq_zero] at e
      rcases mul_eq_zero.mp e with e | e
      · exact absurd e (by positivity)
      · exact e

end Paper970

end Yamagishi
