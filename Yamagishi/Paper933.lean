/-
論文933『流れのある槽で増え続けられる境は最大の増え方ではなく流れ込む餌で決まり、
産出は境の手前で最大になる』の格上げ（一般の形）。

日本語の一文：モノーの式の連続培養で、菌が残れる流れの境は流れ込む餌の濃さで決まり、
産出を最大にする流れはどの値でも境の半分と境のあいだにあり、その比は Ks/S₀ だけで決まる。
English: In the Monod chemostat, a positive steady state exists exactly below D_c = μ(S₀); the
output D·X* has a unique maximiser D_opt = D_c/(1 + √a), a = Ks/(Ks + S₀), so D_c/2 < D_opt < D_c
for all parameters, and the ratio depends only on Ks/S₀.

原稿（933_yamagishi_washout_in_a_flow_through_culture_is_set_by_the_incoming_feed/…_jp.tex）は、
μmax = 0.40、Ks = 0.5、Y = 0.5、S₀ = 10 の一組で、境 0.380952、産出の最大 0.312713（境の 0.820871 倍）、
産出 1.283485 を出し、格子の探索と時間積分で確かめている。D_opt の式は引用で、比の一般の形は無い。

ここで証明した言明（μmax, Ks, S₀, Y > 0）：
  (1) `steady_iff`：X > 0 の点で右辺が 0 ⇔ D < μmax、S = S*(D) = Ks D/(μmax − D)、X = Y(S₀ − S*)。
      `positive_steady_iff`：S ≥ 0、X > 0 の定常が在る ⇔ D < D_c = μ(S₀)（境は μmax でない）。
  (2) `P_le`・`P_lt`：0 < D < μmax で産出 P(D) = D·X*(D) ≤ P(D_opt)、D ≠ D_opt なら真に小さい。
      `P_Dopt`：最大の産出は Y μmax (√(S₀ + Ks) − √Ks)²。
  (3) `Dopt_eq`：D_opt = μmax(1 − √a) = D_c/(1 + √a)。
      `Dopt_bounds`：D_c/2 < D_opt < D_c（どの μmax, Ks, S₀, Y でも）。
      `ratio_depends_only_on`：比 D_opt/D_c は ρ = Ks/S₀ だけの式 1/(1 + √(ρ/(1 + ρ)))。
  (4) `paper_ratio`：原稿の一組で比は 0.82087 と 0.82088 のあいだ（原稿の 0.820871）。
足した仮定：モノーの式と、槽の二つの式（dS/dt = D(S₀ − S) − μX/Y、dX/dt = (μ − D)X）を定義として
置いた。定常は右辺が 0 になる点として扱い、時間の解の振る舞い（引きつけること、落ち着くまでの時間）は
形式化していない。
形式化していないもの：落ち着くまでの時間が境の近くで延びること、数表の積分、分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper933

open Real

/-- モノーの式 μ(S) = μmax S/(Ks + S)。 -/
noncomputable def mu (μm Ks S : ℝ) : ℝ := μm * S / (Ks + S)

/-- 洗い出しの境 D_c = μ(S₀)。 -/
noncomputable def Dc (μm Ks S0 : ℝ) : ℝ := mu μm Ks S0

/-- 定常の餌 S*(D) = Ks D/(μmax − D)。 -/
noncomputable def Sstar (μm Ks D : ℝ) : ℝ := Ks * D / (μm - D)

/-- 定常の菌体 X*(D) = Y(S₀ − S*(D))。 -/
noncomputable def Xstar (μm Ks S0 Y D : ℝ) : ℝ := Y * (S0 - Sstar μm Ks D)

/-- 産出 P(D) = D·X*(D)。 -/
noncomputable def P (μm Ks S0 Y D : ℝ) : ℝ := D * Xstar μm Ks S0 Y D

/-- a = Ks/(Ks + S₀)。 -/
noncomputable def a (Ks S0 : ℝ) : ℝ := Ks / (Ks + S0)

/-- 産出を最大にする希釈率 D_opt = μmax(1 − √a)。 -/
noncomputable def Dopt (μm Ks S0 : ℝ) : ℝ := μm * (1 - √(a Ks S0))

/-- 槽の式の右辺（餌）。 -/
noncomputable def fS (μm Ks S0 Y D S X : ℝ) : ℝ := D * (S0 - S) - mu μm Ks S * X / Y

/-- 槽の式の右辺（菌体）。 -/
noncomputable def fX (μm Ks D S X : ℝ) : ℝ := (mu μm Ks S - D) * X

/-! ### 定常と洗い出しの境 -/

/-- S ≥ 0 で μ(S) = D ⇔ D < μmax かつ S = S*(D)（D ≥ 0）。 -/
theorem mu_eq_iff {μm Ks D S : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    mu μm Ks S = D ↔ D < μm ∧ S = Sstar μm Ks D := by
  unfold mu Sstar
  have hKS : 0 < Ks + S := by linarith
  constructor
  · intro h
    have e : μm * S = D * (Ks + S) := by
      rw [div_eq_iff (ne_of_gt hKS)] at h; linarith
    have hlt : D < μm := by
      by_contra hle
      push Not at hle
      nlinarith
    refine ⟨hlt, ?_⟩
    rw [eq_div_iff (by linarith)]
    linarith
  · rintro ⟨hlt, rfl⟩
    have hu : 0 < μm - D := by linarith
    field_simp
    ring

/-- X > 0 の点で右辺が 0 ⇔ D < μmax、S = S*、X = X*（D > 0。D = 0 では X が決まらない）。 -/
theorem steady_iff {μm Ks S0 Y D S X : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hY : 0 < Y)
    (hS : 0 ≤ S) (hD : 0 < D) (hX : 0 < X) :
    (fS μm Ks S0 Y D S X = 0 ∧ fX μm Ks D S X = 0) ↔
      (D < μm ∧ S = Sstar μm Ks D ∧ X = Xstar μm Ks S0 Y D) := by
  unfold fS fX
  constructor
  · rintro ⟨h1, h2⟩
    have hmu : mu μm Ks S = D := by
      have := (mul_eq_zero.mp h2).resolve_right (ne_of_gt hX)
      linarith
    obtain ⟨hlt, hSe⟩ := (mu_eq_iff hμ hK hS hD.le).mp hmu
    refine ⟨hlt, hSe, ?_⟩
    rw [hmu] at h1
    unfold Xstar
    rw [← hSe]
    have h3 : D * ((S0 - S) * Y) = D * X := by
      field_simp at h1; linarith
    have := mul_left_cancel₀ (ne_of_gt hD) h3
    linarith
  · rintro ⟨hlt, hSe, hXe⟩
    have hmu : mu μm Ks S = D := (mu_eq_iff hμ hK hS hD.le).mpr ⟨hlt, hSe⟩
    rw [hmu, sub_self, zero_mul]
    refine ⟨?_, rfl⟩
    rw [hXe]; unfold Xstar; rw [← hSe]
    field_simp
    ring

/-- 境 D_c は μmax より真に小さい。 -/
theorem Dc_lt {μm Ks S0 : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) : Dc μm Ks S0 < μm := by
  unfold Dc mu
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

theorem Dc_pos {μm Ks S0 : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) : 0 < Dc μm Ks S0 := by
  unfold Dc mu; positivity

/-- 0 < D < μmax で、X* > 0 ⇔ D < D_c。 -/
theorem Xstar_pos_iff {μm Ks S0 Y D : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) (hY : 0 < Y)
    (hDμ : D < μm) :
    0 < Xstar μm Ks S0 Y D ↔ D < Dc μm Ks S0 := by
  unfold Xstar Sstar Dc mu
  have hu : 0 < μm - D := by linarith
  rw [mul_pos_iff_of_pos_left hY, sub_pos, div_lt_iff₀ hu, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- (1) S ≥ 0、X > 0 の定常が在る ⇔ D < D_c（境は μmax ではなく μ(S₀)）。 -/
theorem positive_steady_iff {μm Ks S0 Y D : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0)
    (hY : 0 < Y) (hD : 0 < D) :
    (∃ S X, 0 ≤ S ∧ 0 < X ∧ fS μm Ks S0 Y D S X = 0 ∧ fX μm Ks D S X = 0) ↔
      D < Dc μm Ks S0 := by
  constructor
  · rintro ⟨S, X, hS, hX, h1, h2⟩
    obtain ⟨hlt, _, hXe⟩ := (steady_iff hμ hK hY hS hD hX).mp ⟨h1, h2⟩
    rw [← Xstar_pos_iff hK hS0 hY hlt, ← hXe]
    exact hX
  · intro h
    have hlt : D < μm := h.trans (Dc_lt hμ hK hS0)
    refine ⟨Sstar μm Ks D, Xstar μm Ks S0 Y D, ?_, (Xstar_pos_iff hK hS0 hY hlt).mpr h, ?_⟩
    · unfold Sstar; apply div_nonneg (by positivity) (by linarith)
    · exact (steady_iff hμ hK hY (by unfold Sstar; apply div_nonneg (by positivity) (by linarith))
        hD ((Xstar_pos_iff hK hS0 hY hlt).mpr h)).mpr ⟨hlt, rfl, rfl⟩

/-! ### 産出の最大 -/

/-- u = μmax − D と置いた産出の形：P = Y[μmax(S₀ + 2Ks) − 2μmax AB − (Au − Bμmax)²/u]、
A = √(S₀ + Ks)、B = √Ks。 -/
theorem P_eq {μm Ks S0 Y D : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) (hDμ : D < μm) :
    P μm Ks S0 Y D = Y * (μm * (S0 + 2 * Ks) - 2 * μm * (√(S0 + Ks) * √Ks)
      - (√(S0 + Ks) * (μm - D) - √Ks * μm) ^ 2 / (μm - D)) := by
  have hu : 0 < μm - D := by linarith
  have hA : √(S0 + Ks) ^ 2 = S0 + Ks := sq_sqrt (by linarith)
  have hB : √Ks ^ 2 = Ks := sq_sqrt hK.le
  unfold P Xstar Sstar
  field_simp
  linear_combination (Y * (μm - D) ^ 2) * hA + (Y * μm ^ 2) * hB

/-- √a = √Ks/√(Ks + S₀)。 -/
theorem sqrt_a {Ks S0 : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) :
    √(a Ks S0) = √Ks / √(S0 + Ks) := by
  unfold a
  rw [sqrt_div' _ (by linarith : (0 : ℝ) ≤ Ks + S0), add_comm Ks S0]

/-- 0 < √a < 1。 -/
theorem sqrt_a_bounds {Ks S0 : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) :
    0 < √(a Ks S0) ∧ √(a Ks S0) < 1 := by
  have h0 : 0 < a Ks S0 := by unfold a; positivity
  have h1 : a Ks S0 < 1 := by unfold a; rw [div_lt_one (by linarith)]; linarith
  exact ⟨sqrt_pos.mpr h0, (sqrt_lt' one_pos).mpr (by simpa using h1)⟩

/-- D_opt で Au − Bμmax = 0（u = μmax − D_opt = μmax √a）。 -/
theorem gap_Dopt {μm Ks S0 : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) :
    √(S0 + Ks) * (μm - Dopt μm Ks S0) - √Ks * μm = 0 := by
  have hA : 0 < √(S0 + Ks) := sqrt_pos.mpr (by linarith)
  unfold Dopt
  rw [sqrt_a hK hS0]
  field_simp
  ring

/-- (2) 最大の産出 P(D_opt) = Y μmax (√(S₀ + Ks) − √Ks)²。 -/
theorem P_Dopt {μm Ks S0 Y : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) :
    P μm Ks S0 Y (Dopt μm Ks S0) = Y * μm * (√(S0 + Ks) - √Ks) ^ 2 := by
  have hlt : Dopt μm Ks S0 < μm := by
    unfold Dopt
    have := (sqrt_a_bounds hK hS0).1
    nlinarith
  rw [P_eq hK hS0 hlt, gap_Dopt hK hS0]
  have hA : √(S0 + Ks) ^ 2 = S0 + Ks := sq_sqrt (by linarith)
  have hB : √Ks ^ 2 = Ks := sq_sqrt hK.le
  have e : (√(S0 + Ks) - √Ks) ^ 2 = √(S0 + Ks) ^ 2 - 2 * (√(S0 + Ks) * √Ks) + √Ks ^ 2 := by
    ring
  rw [e, hA, hB]
  ring

/-- (2) 0 < D < μmax で P(D) ≤ P(D_opt)。 -/
theorem P_le {μm Ks S0 Y D : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) (hY : 0 < Y)
    (hDμ : D < μm) :
    P μm Ks S0 Y D ≤ P μm Ks S0 Y (Dopt μm Ks S0) := by
  have hlt : Dopt μm Ks S0 < μm := by
    unfold Dopt
    have := (sqrt_a_bounds hK hS0).1
    nlinarith
  rw [P_eq hK hS0 hDμ, P_eq hK hS0 hlt, gap_Dopt hK hS0]
  have hu : 0 < μm - D := by linarith
  have : 0 ≤ (√(S0 + Ks) * (μm - D) - √Ks * μm) ^ 2 / (μm - D) := by positivity
  have h2 : (0 : ℝ) ^ 2 / (μm - Dopt μm Ks S0) = 0 := by simp
  rw [h2]
  apply mul_le_mul_of_nonneg_left _ hY.le
  linarith

/-- (2) D ≠ D_opt なら真に小さい（最大はただ一つ）。 -/
theorem P_lt {μm Ks S0 Y D : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) (hY : 0 < Y)
    (hDμ : D < μm) (hne : D ≠ Dopt μm Ks S0) :
    P μm Ks S0 Y D < P μm Ks S0 Y (Dopt μm Ks S0) := by
  have hlt : Dopt μm Ks S0 < μm := by
    unfold Dopt
    have := (sqrt_a_bounds hK hS0).1
    nlinarith
  rw [P_eq hK hS0 hDμ, P_eq hK hS0 hlt, gap_Dopt hK hS0]
  have hu : 0 < μm - D := by linarith
  have hA : 0 < √(S0 + Ks) := sqrt_pos.mpr (by linarith)
  have hgap : √(S0 + Ks) * (μm - D) - √Ks * μm ≠ 0 := by
    intro h0
    apply hne
    have e := gap_Dopt (μm := μm) hK hS0
    have : √(S0 + Ks) * (μm - D) = √(S0 + Ks) * (μm - Dopt μm Ks S0) := by linarith
    have := mul_left_cancel₀ (ne_of_gt hA) this
    linarith
  have : 0 < (√(S0 + Ks) * (μm - D) - √Ks * μm) ^ 2 / (μm - D) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hgap))) hu
  have h2 : (0 : ℝ) ^ 2 / (μm - Dopt μm Ks S0) = 0 := by simp
  rw [h2]
  apply mul_lt_mul_of_pos_left _ hY
  linarith

/-! ### 境との比 -/

/-- D_c = μmax(1 − a)。 -/
theorem Dc_eq {μm Ks S0 : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) : Dc μm Ks S0 = μm * (1 - a Ks S0) := by
  unfold Dc mu a
  field_simp
  ring

/-- (3) D_opt = D_c/(1 + √a)。 -/
theorem Dopt_eq {μm Ks S0 : ℝ} (hK : 0 < Ks) (hS0 : 0 < S0) :
    Dopt μm Ks S0 = Dc μm Ks S0 / (1 + √(a Ks S0)) := by
  have h0 := (sqrt_a_bounds hK hS0).1
  have ha : √(a Ks S0) ^ 2 = a Ks S0 := sq_sqrt (by unfold a; positivity)
  rw [Dc_eq hK hS0, Dopt, eq_div_iff (by linarith)]
  linear_combination (-μm) * ha

/-- (3) どの値でも D_c/2 < D_opt < D_c。 -/
theorem Dopt_bounds {μm Ks S0 : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) :
    Dc μm Ks S0 / 2 < Dopt μm Ks S0 ∧ Dopt μm Ks S0 < Dc μm Ks S0 := by
  obtain ⟨h0, h1⟩ := sqrt_a_bounds hK hS0
  have hc := Dc_pos hμ hK hS0
  rw [Dopt_eq hK hS0]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- (3) 比 D_opt/D_c は ρ = Ks/S₀ だけで決まる（μmax と Y によらない）。 -/
theorem ratio_depends_only_on {μm Ks S0 : ℝ} (hμ : 0 < μm) (hK : 0 < Ks) (hS0 : 0 < S0) :
    Dopt μm Ks S0 / Dc μm Ks S0 = 1 / (1 + √((Ks / S0) / (1 + Ks / S0))) := by
  have hc := Dc_pos hμ hK hS0
  have e : (Ks / S0) / (1 + Ks / S0) = a Ks S0 := by
    unfold a; field_simp; ring
  rw [e, Dopt_eq hK hS0]
  have := (sqrt_a_bounds hK hS0).1
  field_simp

/-- (4) 原稿の一組（Ks = 0.5、S₀ = 10）で比は 0.82087 と 0.82088 のあいだ。 -/
theorem paper_ratio :
    0.82087 < Dopt 0.4 0.5 10 / Dc 0.4 0.5 10 ∧ Dopt 0.4 0.5 10 / Dc 0.4 0.5 10 < 0.82088 := by
  rw [ratio_depends_only_on (by norm_num) (by norm_num) (by norm_num)]
  have e : ((0.5 : ℝ) / 10) / (1 + 0.5 / 10) = 1 / 21 := by norm_num
  rw [e]
  have hl : (0.218217 : ℝ) < √(1 / 21) := by
    rw [lt_sqrt (by norm_num)]; norm_num
  have hu : √(1 / 21 : ℝ) < 0.218218 := by
    rw [sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

end Paper933

end Yamagishi
