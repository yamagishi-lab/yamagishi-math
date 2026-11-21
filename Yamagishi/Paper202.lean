/-
論文202『接続は計量から導かれない。二つの要求が選ばれて、はじめて一つに決まる』の格上げ（一般の形・各点の線形代数の芯）。

原稿（202_yamagishi_connection_is_a_choice/…_jp.tex）は、d = 2〜5 で係数行列の階数を数値で測り、
計量を保つ接続の自由度 2, 9, 24, 50 と捩率の成分の数の一致を確かめ、直線（測地線）を動かさない
自由度を d = 2〜6 で数値に測って C(d, 3) と一致させている。

ここで証明した言明（各点で、K はレヴィ＝チヴィタからの差の、添字を下げたもの K_abc。d は任意）：
  (1) `contorsion_spec`・`contorsion_unique`：計量両立（K_abc = −K_bac と置く）な K と、
      後ろ二つの添字で反対称な捩率 T_abc = K_abc − K_acb は一対一に対応する。
      逆向きの式は K_abc = (T_abc + T_bca − T_cab)/2。
  (2) `geodesic_iff`：すべての速度 v で K_abc v^b v^c = 0（径数つきの測地線の式の二次の項が変わらない）
      ⇔ K_abc + K_acb = 0（後ろ二つで反対称）。
  (3) `totally_antisymm`：計量両立で (2) を満たす K は全反対称。`geodesic_iff_torsion`：計量両立な K が
      (2) を満たす ⇔ 捩率 T が全反対称（そのとき T = 2K）。
  (4) `d_two`：d = 2 では、計量両立で (2) を満たす K は 0。レヴィ＝チヴィタ以外の計量両立な接続は
      どれも、ある速度で測地線の式を変える。
定義に置いたもの：計量両立の条件を、下げた添字の K_abc = −K_bac とした（計量で添字を下げる約束）。
形式化していないもの：自由度の数 d²(d − 1)/2 と C(d, 3) の数え上げ、多様体の上の接続、
「二次の項が同じ ⇔ 測地線が同じ」のうち測地線の存在を使う向き、射影的に同じ測地線。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper202

variable {d : ℕ}

/-- 添字を下げた接続の差 K_abc（各点の成分）。 -/
abbrev Tensor3 (d : ℕ) := Fin d → Fin d → Fin d → ℝ

/-- 計量両立：前の二つの添字で反対称。 -/
def MetricCompat (K : Tensor3 d) : Prop := ∀ a b c, K a b c = -K b a c

/-- 捩率 T_abc = K_abc − K_acb。 -/
def torsion (K : Tensor3 d) : Tensor3 d := fun a b c => K a b c - K a c b

/-- 捩率から戻す式 K_abc = (T_abc + T_bca − T_cab)/2。 -/
noncomputable def contorsion (T : Tensor3 d) : Tensor3 d :=
  fun a b c => (T a b c + T b c a - T c a b) / 2

/-- (1) 後ろ二つで反対称な T から作った K は計量両立で、その捩率は T。 -/
theorem contorsion_spec (T : Tensor3 d) (hT : ∀ a b c, T a b c = -T a c b) :
    MetricCompat (contorsion T) ∧ torsion (contorsion T) = T := by
  constructor
  · intro a b c
    simp only [contorsion]
    rw [hT b c a, hT a b c, hT c a b]
    ring
  · funext a b c
    simp only [torsion, contorsion]
    rw [hT c a b, hT b a c, hT a c b]
    ring

/-- (1) 捩率が同じ計量両立な K は等しい。 -/
theorem contorsion_unique {K K' : Tensor3 d} (hK : MetricCompat K) (hK' : MetricCompat K')
    (h : torsion K = torsion K') : K = K' := by
  -- L = K − K' は前の二つで反対称、後ろ二つで対称
  set L : Tensor3 d := fun a b c => K a b c - K' a b c
  have hL1 : ∀ a b c, L a b c = -L b a c := by
    intro a b c; simp only [L]; rw [hK a b c, hK' a b c]; ring
  have hL2 : ∀ a b c, L a b c = L a c b := by
    intro a b c
    have := congrFun (congrFun (congrFun h a) b) c
    simp only [torsion] at this
    simp only [L]; linarith
  have hL0 : ∀ a b c, L a b c = 0 := by
    intro a b c
    have e1 := hL1 a b c
    have e2 := hL2 b a c
    have e3 := hL1 b c a
    have e4 := hL2 c b a
    have e5 := hL1 c a b
    have e6 := hL2 a c b
    linarith
  funext a b c
  have := hL0 a b c
  simp only [L] at this
  linarith

/-- 二次の項 K_abc v^b v^c。 -/
def quad (K : Tensor3 d) (a : Fin d) (v : Fin d → ℝ) : ℝ := ∑ b, ∑ c, K a b c * v b * v c

theorem quad_single_add (K : Tensor3 d) (a b c : Fin d) :
    quad K a (Pi.single b 1 + Pi.single c 1) - quad K a (Pi.single b 1) -
      quad K a (Pi.single c 1) = K a b c + K a c b := by
  simp only [quad, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  simp [Pi.single_apply]
  ring

/-- (2) 二次の項がどの速度でも 0 ⇔ 後ろ二つで反対称。 -/
theorem geodesic_iff (K : Tensor3 d) :
    (∀ a v, quad K a v = 0) ↔ ∀ a b c, K a b c + K a c b = 0 := by
  constructor
  · intro h a b c
    rw [← quad_single_add, h, h, h]; ring
  · intro h a v
    unfold quad
    have : ∑ b, ∑ c, K a b c * v b * v c = ∑ b, ∑ c, K a c b * v c * v b := by
      rw [Finset.sum_comm]
    have h2 : ∑ b, ∑ c, K a b c * v b * v c = -∑ b, ∑ c, K a b c * v b * v c := by
      conv_rhs => rw [this]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro b _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro c _
      have := h a b c
      rw [show K a c b = -K a b c by linarith]
      ring
    linarith

/-- (3) 計量両立で後ろ二つでも反対称なら、全反対称（前と後ろの入れ替えでも符号が変わる）。 -/
theorem totally_antisymm {K : Tensor3 d} (hK : MetricCompat K)
    (hg : ∀ a b c, K a b c + K a c b = 0) : ∀ a b c, K a b c = -K c b a := by
  intro a b c
  have e1 := hK a b c
  have e2 := hg b a c
  have e3 := hK b c a
  linarith

/-- (3) 計量両立な K について、二次の項が変わらない ⇔ 捩率が全反対称。 -/
theorem geodesic_iff_torsion {K : Tensor3 d} (hK : MetricCompat K) :
    (∀ a v, quad K a v = 0) ↔
      (∀ a b c, torsion K a b c = -torsion K b a c ∧ torsion K a b c = -torsion K a c b) := by
  rw [geodesic_iff]
  constructor
  · intro hg a b c
    simp only [torsion]
    have := hK a b c; have := hK a c b; have := hK b c a; have := hK c a b
    have := hg a b c; have := hg b a c; have := hg b c a
    constructor <;> linarith
  · intro hT a b c
    obtain ⟨h1, h2⟩ := hT a b c
    obtain ⟨h3, h4⟩ := hT b a c
    obtain ⟨h5, h6⟩ := hT c a b
    simp only [torsion] at *
    have := hK a b c; have := hK a c b; have := hK b c a; have := hK c a b
    have := hK b a c; have := hK c b a
    linarith

/-- (4) d = 2 では、計量両立で二次の項を変えない K は 0。 -/
theorem d_two {K : Tensor3 2} (hK : MetricCompat K) (hg : ∀ a v, quad K a v = 0) : K = 0 := by
  have hg' := (geodesic_iff K).1 hg
  funext a b c
  have h1 := hK a b c
  have h2 := hg' a b c
  have hab : ∀ x y z : Fin 2, x = y ∨ y = z ∨ x = z := by decide
  rcases hab a b c with rfl | rfl | rfl
  · simp; linarith
  · simp; linarith
  · have := totally_antisymm hK hg' a b a
    simp; linarith

end Paper202

end Yamagishi
