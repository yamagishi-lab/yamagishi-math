/-
論文962『胴の板と空洞の二つの共鳴は、どう板を合わせても、空気だけをばねにした板の高さより近づかない』
の格上げ（一般の形）。

日本語の一文：首の空気と壁の板を空洞の空気のばねで結んだ模型では、どの正の値でも二つの共鳴は
ω₁ω₂ = ω_H ω_v と (ω₂ − ω₁)² = (ω_H − ω_v)² + ω_a² を満たし、差は ω_a より小さくならない。
English: In the two-oscillator model (neck air and piston plate coupled by the cavity air spring),
for all positive parameters the two normal-mode frequencies satisfy ω₁ω₂ = ω_Hω_v and
(ω₂ − ω₁)² = (ω_H − ω_v)² + ω_a², lie strictly outside ω_H and ω_b, and differ by at least ω_a,
with equality iff ω_v = ω_H.

原稿（962_yamagishi_air_and_plate_resonances_never_come_closer_than_the_air_spring_frequency/…_jp.tex）
は、一つの空洞と一枚の板で f_v を七通りに置いて数値の固有値を出し、和・積・斜辺の式と突き合わせ、
差の最小を黄金分割の探索で 53.487201 Hz（= f_a）と求めている。式は第1節に書いてあるが導いていない。

ここで証明した言明（m_n, m_p, S_n, S_p, κ, k_p > 0、ω_H² = S_n²κ/m_n、ω_v² = k_p/m_p、
ω_a² = S_p²κ/m_p、ω_b² = ω_v² + ω_a²）：
  (1) `mode_iff`：模型の式 m_n ẍ = S_n p、m_p ÿ = −k_p y + S_p p、p = −κ(S_n x + S_p y) が角振動数 ω の
      0 でない振動を持つ ⇔ λ = ω² が λ² − (ω_H² + ω_b²)λ + ω_H²ω_v² = 0 を満たす。
  (2) `two_modes`：正の解はちょうど二つ（ω₁ < ω₂）。
  (3) `sum_prod`：ω₁² + ω₂² = ω_H² + ω_b²、ω₁ω₂ = ω_H ω_v。
      `gap_sq`：(ω₂ − ω₁)² = (ω_H − ω_v)² + ω_a²（直角三角形の斜辺）。
  (4) `push_apart`：ω₁ < min(ω_H, ω_b)、ω₂ > max(ω_H, ω_b)（等号なし）。
  (5) `gap_ge`：ω₂ − ω₁ ≥ ω_a。`gap_eq_iff`：等号 ⇔ ω_v = ω_H（最小の差は ω_H によらない）。
      `gap_closed_tuned`：穴をふさいだ板の高さ ω_b を ω_H にそろえると差は ω_a より真に大きい。
足した仮定：板はピストンのように一つの形で動き、損失と放射を入れない模型の式を定義として置いた
（原稿と同じ）。振動は x = X cos ωt の形の解として、振幅の一次方程式で扱った。
形式化していないもの：原稿の数表と黄金分割の探索、比 1.014121 の値、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper962

open Real

/-! ### 模型の式から固有振動の条件へ -/

/-- 振幅 (X, Y) の式：−ω² m_n X = S_n p、−ω² m_p Y = −k_p Y + S_p p、p = −κ(S_n X + S_p Y)。 -/
def IsMode (mn mp Sn Sp κ kp ω X Y : ℝ) : Prop :=
  -(ω ^ 2) * mn * X = Sn * (-(κ * (Sn * X + Sp * Y))) ∧
    -(ω ^ 2) * mp * Y = -(kp * Y) + Sp * (-(κ * (Sn * X + Sp * Y)))

/-- 固有振動の条件の多項式 λ² − (ω_H² + ω_v² + ω_a²)λ + ω_H²ω_v²（引数は二乗の値）。 -/
def charpoly (H2 v2 a2 lam : ℝ) : ℝ := lam ^ 2 - (H2 + v2 + a2) * lam + H2 * v2

/-- (1) 0 でない振動が在る ⇔ ω² が条件の多項式の根。 -/
theorem mode_iff {mn mp Sn Sp κ kp : ℝ} (hmn : 0 < mn) (hmp : 0 < mp) (hSn : 0 < Sn)
    (hSp : 0 < Sp) (hκ : 0 < κ) (ω : ℝ) :
    (∃ X Y, (X ≠ 0 ∨ Y ≠ 0) ∧ IsMode mn mp Sn Sp κ kp ω X Y) ↔
      charpoly (Sn ^ 2 * κ / mn) (kp / mp) (Sp ^ 2 * κ / mp) (ω ^ 2) = 0 := by
  set a11 := Sn ^ 2 * κ - ω ^ 2 * mn
  set a12 := Sn * Sp * κ
  set a22 := kp + Sp ^ 2 * κ - ω ^ 2 * mp
  have hdet : charpoly (Sn ^ 2 * κ / mn) (kp / mp) (Sp ^ 2 * κ / mp) (ω ^ 2) =
      (a11 * a22 - a12 ^ 2) / (mn * mp) := by
    unfold charpoly
    simp only [a11, a12, a22]
    field_simp
    ring
  have hmode : ∀ X Y, IsMode mn mp Sn Sp κ kp ω X Y ↔
      (a11 * X + a12 * Y = 0 ∧ a12 * X + a22 * Y = 0) := by
    intro X Y
    unfold IsMode
    simp only [a11, a12, a22]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [hdet, div_eq_zero_iff, or_iff_left (by positivity)]
  constructor
  · rintro ⟨X, Y, hne, hm⟩
    obtain ⟨h1, h2⟩ := (hmode X Y).mp hm
    by_contra hd
    have hX : (a11 * a22 - a12 ^ 2) * X = 0 := by linear_combination a22 * h1 - a12 * h2
    have hY : (a11 * a22 - a12 ^ 2) * Y = 0 := by linear_combination a11 * h2 - a12 * h1
    rcases hne with hx | hy
    · exact hx ((mul_eq_zero.mp hX).resolve_left hd)
    · exact hy ((mul_eq_zero.mp hY).resolve_left hd)
  · intro hd
    refine ⟨-a12, a11, Or.inl (neg_ne_zero.mpr (by simp only [a12]; positivity)),
      (hmode _ _).mpr ⟨by ring, ?_⟩⟩
    linear_combination hd

/-! ### 二つの根の性質（H = ω_H、v = ω_v、a = ω_a、どれも正） -/

/-- ω を角振動数として、ω² が根であること。 -/
def IsRoot (H v a ω : ℝ) : Prop := charpoly (H ^ 2) (v ^ 2) (a ^ 2) (ω ^ 2) = 0

/-- (2) 正の解はちょうど二つ。 -/
theorem two_modes {H v a : ℝ} (hH : 0 < H) (hv : 0 < v) (ha : 0 < a) :
    ∃ ω₁ ω₂, 0 < ω₁ ∧ ω₁ < ω₂ ∧ IsRoot H v a ω₁ ∧ IsRoot H v a ω₂ ∧
      ∀ ω, 0 < ω → IsRoot H v a ω → ω = ω₁ ∨ ω = ω₂ := by
  set T := H ^ 2 + v ^ 2 + a ^ 2
  set P := H ^ 2 * v ^ 2
  set D := T ^ 2 - 4 * P
  have hD : 0 < D := by
    simp only [D, T, P]
    nlinarith [sq_nonneg (H ^ 2 - v ^ 2), sq_pos_of_pos ha, mul_pos (sq_pos_of_pos ha)
      (add_pos (sq_pos_of_pos hH) (sq_pos_of_pos hv))]
  have hsD : √D ^ 2 = D := sq_sqrt hD.le
  have hsDpos : 0 < √D := sqrt_pos.mpr hD
  have hP : 0 < P := by positivity
  have hT : 0 < T := by positivity
  have hTD : √D < T := by
    rw [sqrt_lt' hT]; simp only [D]; linarith
  set l1 := (T - √D) / 2
  set l2 := (T + √D) / 2
  have hl1 : 0 < l1 := by simp only [l1]; linarith
  have hl12 : l1 < l2 := by simp only [l1, l2]; linarith
  have hfac : ∀ lam, charpoly (H ^ 2) (v ^ 2) (a ^ 2) lam = (lam - l1) * (lam - l2) := by
    intro lam
    unfold charpoly
    simp only [l1, l2]
    have : T ^ 2 - √D ^ 2 = 4 * P := by rw [hsD]; simp only [D]; ring
    linear_combination (-1 / 4 : ℝ) * this
  refine ⟨√l1, √l2, sqrt_pos.mpr hl1, sqrt_lt_sqrt hl1.le hl12, ?_, ?_, ?_⟩
  · unfold IsRoot; rw [sq_sqrt hl1.le, hfac]; ring
  · unfold IsRoot; rw [sq_sqrt (hl1.trans hl12).le, hfac]; ring
  · intro ω hω hr
    unfold IsRoot at hr
    rw [hfac] at hr
    rcases mul_eq_zero.mp hr with h | h
    · left; rw [← sqrt_sq hω.le]; congr 1; linarith
    · right; rw [← sqrt_sq hω.le]; congr 1; linarith

/-- 二つの異なる根の和と積（ヴィエタ）。 -/
theorem vieta {H v a ω₁ ω₂ : ℝ} (h0 : 0 < ω₁) (h12 : ω₁ < ω₂)
    (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    ω₁ ^ 2 + ω₂ ^ 2 = H ^ 2 + v ^ 2 + a ^ 2 ∧ ω₁ ^ 2 * ω₂ ^ 2 = H ^ 2 * v ^ 2 := by
  unfold IsRoot charpoly at r1 r2
  have hne : ω₁ ^ 2 - ω₂ ^ 2 ≠ 0 := by nlinarith
  have hs : ω₁ ^ 2 + ω₂ ^ 2 = H ^ 2 + v ^ 2 + a ^ 2 := by
    have : (ω₁ ^ 2 - ω₂ ^ 2) * (ω₁ ^ 2 + ω₂ ^ 2 - (H ^ 2 + v ^ 2 + a ^ 2)) = 0 := by
      linear_combination r1 - r2
    have := (mul_eq_zero.mp this).resolve_left hne
    linarith
  refine ⟨hs, ?_⟩
  have : ω₁ ^ 2 * ω₂ ^ 2 = ω₁ ^ 2 * (H ^ 2 + v ^ 2 + a ^ 2 - ω₁ ^ 2) := by rw [← hs]; ring
  rw [this]
  linear_combination -r1

/-- (3) 和と積：ω₁² + ω₂² = ω_H² + ω_b²、ω₁ω₂ = ω_H ω_v。 -/
theorem sum_prod {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (h0 : 0 < ω₁) (h12 : ω₁ < ω₂)
    (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    ω₁ ^ 2 + ω₂ ^ 2 = H ^ 2 + (v ^ 2 + a ^ 2) ∧ ω₁ * ω₂ = H * v := by
  obtain ⟨hs, hp⟩ := vieta h0 h12 r1 r2
  refine ⟨by linarith, ?_⟩
  have h2 : 0 < ω₂ := h0.trans h12
  have : (ω₁ * ω₂) ^ 2 = (H * v) ^ 2 := by rw [mul_pow, mul_pow]; exact hp
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp this

/-- (3) 差の二乗は斜辺：(ω₂ − ω₁)² = (ω_H − ω_v)² + ω_a²。 -/
theorem gap_sq {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (h0 : 0 < ω₁) (h12 : ω₁ < ω₂)
    (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    (ω₂ - ω₁) ^ 2 = (H - v) ^ 2 + a ^ 2 := by
  obtain ⟨hs, hp⟩ := sum_prod hH hv h0 h12 r1 r2
  linear_combination hs - 2 * hp

/-- 条件の多項式を、根の位置で書く。 -/
theorem charpoly_factor {H v a ω₁ ω₂ : ℝ} (h0 : 0 < ω₁) (h12 : ω₁ < ω₂)
    (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) (lam : ℝ) :
    charpoly (H ^ 2) (v ^ 2) (a ^ 2) lam = (lam - ω₁ ^ 2) * (lam - ω₂ ^ 2) := by
  obtain ⟨hs, hp⟩ := vieta h0 h12 r1 r2
  unfold charpoly
  linear_combination lam * hs - hp

/-- (4) 押し離し：ω₁ < ω_H < ω₂ と ω₁ < ω_b < ω₂（ω_b² = ω_v² + ω_a²）。 -/
theorem push_apart {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (ha : 0 < a) (h0 : 0 < ω₁)
    (h12 : ω₁ < ω₂) (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    (ω₁ < H ∧ H < ω₂) ∧ (ω₁ < √(v ^ 2 + a ^ 2) ∧ √(v ^ 2 + a ^ 2) < ω₂) := by
  have h2 : 0 < ω₂ := h0.trans h12
  have hsq : ω₁ ^ 2 < ω₂ ^ 2 := by nlinarith
  -- 多項式が負の点は二つの根のあいだ
  have between : ∀ x, 0 < x → charpoly (H ^ 2) (v ^ 2) (a ^ 2) (x ^ 2) < 0 → ω₁ < x ∧ x < ω₂ := by
    intro x hx hneg
    rw [charpoly_factor h0 h12 r1 r2] at hneg
    have hA : ω₁ ^ 2 < x ^ 2 ∧ x ^ 2 < ω₂ ^ 2 := by
      rcases lt_or_ge (x ^ 2) (ω₁ ^ 2) with h | h
      · nlinarith
      rcases lt_or_ge (x ^ 2) (ω₂ ^ 2) with h' | h'
      · constructor
        · rcases eq_or_lt_of_le h with he | hl
          · rw [← he] at hneg; simp at hneg
          · exact hl
        · exact h'
      · nlinarith
    exact ⟨(pow_lt_pow_iff_left₀ h0.le hx.le two_ne_zero).mp hA.1,
      (pow_lt_pow_iff_left₀ hx.le h2.le two_ne_zero).mp hA.2⟩
  have hb : 0 < √(v ^ 2 + a ^ 2) := sqrt_pos.mpr (by positivity)
  refine ⟨between H hH ?_, between _ hb ?_⟩
  · unfold charpoly; nlinarith [mul_pos (sq_pos_of_pos hH) (sq_pos_of_pos ha)]
  · rw [sq_sqrt (by positivity)]
    unfold charpoly
    nlinarith [mul_pos (sq_pos_of_pos hH) (sq_pos_of_pos ha)]

/-- (5) 差は ω_a より小さくならない。 -/
theorem gap_ge {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (ha : 0 < a) (h0 : 0 < ω₁)
    (h12 : ω₁ < ω₂) (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    a ≤ ω₂ - ω₁ := by
  have := gap_sq hH hv h0 h12 r1 r2
  nlinarith [sq_nonneg (H - v)]

/-- (5) 等号 ⇔ ω_v = ω_H。 -/
theorem gap_eq_iff {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (ha : 0 < a) (h0 : 0 < ω₁)
    (h12 : ω₁ < ω₂) (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) :
    ω₂ - ω₁ = a ↔ v = H := by
  have hg := gap_sq hH hv h0 h12 r1 r2
  constructor
  · intro he
    rw [he] at hg
    have : (H - v) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro he
    rw [he, sub_self] at hg
    have : (ω₂ - ω₁) ^ 2 = a ^ 2 := by rw [hg]; ring
    exact (sq_eq_sq₀ (by linarith) ha.le).mp this

/-- (5) 穴をふさいだ板の高さ ω_b を ω_H にそろえると、差は ω_a より真に大きい。 -/
theorem gap_closed_tuned {H v a ω₁ ω₂ : ℝ} (hH : 0 < H) (hv : 0 < v) (ha : 0 < a) (h0 : 0 < ω₁)
    (h12 : ω₁ < ω₂) (r1 : IsRoot H v a ω₁) (r2 : IsRoot H v a ω₂) (hb : v ^ 2 + a ^ 2 = H ^ 2) :
    a < ω₂ - ω₁ := by
  rcases lt_or_eq_of_le (gap_ge hH hv ha h0 h12 r1 r2) with h | h
  · exact h
  · have := (gap_eq_iff hH hv ha h0 h12 r1 r2).mp h.symm
    rw [this] at hb
    nlinarith

end Paper962

end Yamagishi
