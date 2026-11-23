/-
論文598『宝石が光を上へ返す角度の窓は、屈折率 √2 で開き、2.3048 のあたりで最も広い』の確かめと
格上げ（一般の形）。

日本語：真上から入る光を二度全反射させて上から返すパビリオン角の窓は、臨界角 θ_c の区分一次式の
幅をもち、屈折率 n > √2 のときだけ開き、n = 1/sin(π/7) でただ一つの最大 90/7 度（π/14）をとる。
English: The window of pavilion angles that return vertical light after two total reflections has a
piecewise linear width in the critical angle; it opens exactly for n > √2 and is uniquely widest,
90/7 degrees (π/14), at n = 1/sin(π/7).

原稿（598_yamagishi_the_gem_window_opens_at_root_two/…_jp.tex）は、五つの条件
θ > θ_c、θ > 30、180 − 3θ > θ_c、180 − 4θ < θ_c、4θ − 180 < θ_c（度）を書き、窓の幅の三つの範囲の
閉じた式、開く屈折率 √2、最も広い屈折率 2.304765（臨界角 180/7 度）を一般の形で述べ、六つの材質で
光線追跡と突き合わせる。式の導出と単峰性の証明は書いていない。

ここで証明した言明（角度は度、θ_c は臨界角）：
  (1) `window_eq`：五つの条件を満たす θ の集合は開区間 (max(θ_c, (180 − θ_c)/4),
      min((180 − θ_c)/3, (180 + θ_c)/4))。`lower_ge_36`：下端はいつも 36 以上なので、30 度の条件は
      窓の中では効かない（原稿の観察 2.1）。`volume_window`：窓の大きさ（ルベーグ測度）は上端 − 下端。
  (2) `width_high`・`width_mid`・`width_low`：幅は (180 − 4θ_c)/3（36 ≤ θ_c）、(180 − θ_c)/12
      （180/7 ≤ θ_c ≤ 36）、θ_c/2（θ_c ≤ 180/7）。`nonempty_iff`：0 < θ_c のとき、窓が開く ⇔ θ_c < 45。
  (3) `width_le`・`width_eq_max_iff`：幅は 90/7 以下で、等号は θ_c = 180/7 だけ。
      `width_strictMonoOn`・`width_strictAntiOn`：θ_c ≤ 180/7 で狭義に増え、180/7 ≤ θ_c で狭義に減る。
  (4) 屈折率で：θ_c(n) = arcsin(1/n)·180/π。`opens_iff`：n > 1 で、窓が開く ⇔ n > √2。
      `thetaC_eq_iff`：θ_c(n) = 180/7 ⇔ n = 1/sin(π/7)。`width_n_le`・`width_n_eq_max_iff`：幅は
      90/7 度以下で、等号は n = 1/sin(π/7) だけ。`width_n_strictMonoOn`・`width_n_strictAntiOn`：
      √2 ≤ n ≤ 1/sin(π/7) で狭義に増え、n ≥ 1/sin(π/7) で狭義に減る（単峰）。`max_in_radians`：
      90/7 度は π/14。
足した仮定：五つの条件は原稿の模型の式として置いた（光線を向きだけで追う二次元の模型）。
形式化していないもの：五つの条件を反射の幾何から出す所、光線追跡、斜めの光・冠の屈折・分散、
分離子の読み。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper598

open Real Set MeasureTheory

/-! ### (1) 五つの条件と窓 -/

/-- 五つの条件を満たすパビリオン角 θ（度）の集合。 -/
def window (θc : ℝ) : Set ℝ :=
  {θ | θc < θ ∧ 30 < θ ∧ θc < 180 - 3 * θ ∧ 180 - 4 * θ < θc ∧ 4 * θ - 180 < θc}

/-- 窓の下端。 -/
noncomputable def lower (θc : ℝ) : ℝ := max θc ((180 - θc) / 4)

/-- 窓の上端。 -/
noncomputable def upper (θc : ℝ) : ℝ := min ((180 - θc) / 3) ((180 + θc) / 4)

/-- 窓の幅。 -/
noncomputable def width (θc : ℝ) : ℝ := upper θc - lower θc

/-- (1) 下端はいつも 36 度以上。 -/
theorem lower_ge_36 (θc : ℝ) : 36 ≤ lower θc := by
  unfold lower
  have h1 := le_max_left θc ((180 - θc) / 4)
  have h2 := le_max_right θc ((180 - θc) / 4)
  linarith

/-- (1) 五つの条件の集合は開区間（30 度の条件は効かない）。 -/
theorem window_eq (θc : ℝ) : window θc = Ioo (lower θc) (upper θc) := by
  ext θ
  simp only [window, lower, upper, mem_ofPred_eq, mem_Ioo, max_lt_iff, lt_min_iff]
  constructor
  · rintro ⟨h1, _, h3, h4, h5⟩
    refine ⟨⟨h1, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, by linarith, by linarith, by linarith, by linarith⟩

/-- (1) 窓の大きさは上端 − 下端。 -/
theorem volume_window (θc : ℝ) : volume (window θc) = ENNReal.ofReal (width θc) := by
  rw [window_eq, Real.volume_Ioo]; rfl

/-! ### (2) 三つの範囲の閉じた式 -/

theorem width_high {θc : ℝ} (h : 36 ≤ θc) : width θc = (180 - 4 * θc) / 3 := by
  unfold width lower upper
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  ring

theorem width_mid {θc : ℝ} (h1 : 180 / 7 ≤ θc) (h2 : θc ≤ 36) : width θc = (180 - θc) / 12 := by
  unfold width lower upper
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  ring

theorem width_low {θc : ℝ} (h : θc ≤ 180 / 7) : width θc = θc / 2 := by
  unfold width lower upper
  rw [min_eq_right (by linarith)]
  rcases le_total θc ((180 - θc) / 4) with h' | h'
  · rw [max_eq_right h']; ring
  · rw [max_eq_left h']; linarith

/-- (2) 0 < θ_c のとき、窓が開く ⇔ θ_c < 45。 -/
theorem nonempty_iff {θc : ℝ} (hθ : 0 < θc) : (window θc).Nonempty ↔ θc < 45 := by
  rw [window_eq, nonempty_Ioo]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : width θc = (180 - 4 * θc) / 3 := width_high (by linarith)
    unfold width at this
    linarith
  · intro h
    have hw : 0 < width θc := by
      rcases le_total θc (180 / 7) with h1 | h1
      · rw [width_low h1]; linarith
      · rcases le_total θc 36 with h2 | h2
        · rw [width_mid h1 h2]; linarith
        · rw [width_high h2]; linarith
    unfold width at hw
    linarith

/-! ### (3) 幅の最大と単峰性 -/

theorem width_le (θc : ℝ) : width θc ≤ 90 / 7 := by
  rcases le_total θc (180 / 7) with h1 | h1
  · rw [width_low h1]; linarith
  · rcases le_total θc 36 with h2 | h2
    · rw [width_mid h1 h2]; linarith
    · rw [width_high h2]; linarith

theorem width_eq_max_iff (θc : ℝ) : width θc = 90 / 7 ↔ θc = 180 / 7 := by
  constructor
  · intro hw
    rcases lt_trichotomy θc (180 / 7) with h1 | h1 | h1
    · rw [width_low h1.le] at hw; linarith
    · exact h1
    · rcases le_total θc 36 with h2 | h2
      · rw [width_mid h1.le h2] at hw; linarith
      · rw [width_high h2] at hw; linarith
  · intro h; rw [h, width_low le_rfl]; norm_num

theorem width_strictMonoOn : StrictMonoOn width (Iic (180 / 7)) := by
  intro x hx y hy hxy
  rw [mem_Iic] at hx hy
  rw [width_low hx, width_low hy]; linarith

theorem width_strictAntiOn : StrictAntiOn width (Ici (180 / 7)) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  rcases le_total y 36 with hy2 | hy2
  · rw [width_mid hx (by linarith), width_mid hy hy2]; linarith
  · rcases le_total x 36 with hx2 | hx2
    · rw [width_mid hx hx2, width_high hy2]; linarith
    · rw [width_high hx2, width_high hy2]; linarith

/-! ### (4) 屈折率で読む -/

/-- 臨界角（度）θ_c(n) = arcsin(1/n)·180/π。 -/
noncomputable def thetaC (n : ℝ) : ℝ := arcsin (1 / n) * (180 / π)

theorem thetaC_pos {n : ℝ} (hn : 0 < n) : 0 < thetaC n := by
  unfold thetaC
  apply mul_pos (arcsin_pos.mpr (by positivity)) (by positivity)

theorem thetaC_strictAntiOn : StrictAntiOn thetaC (Ici 1) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  unfold thetaC
  apply mul_lt_mul_of_pos_right _ (by positivity)
  apply arcsin_lt_arcsin (by have : 0 < 1 / y := by positivity
                             linarith)
    (one_div_lt_one_div_of_lt (by linarith) hxy)
  rw [div_le_one (by linarith)]; exact hx

/-- (4) θ_c(n) < 45 ⇔ n > √2（n ≥ 1）。 -/
theorem thetaC_lt_45_iff {n : ℝ} (hn : 1 ≤ n) : thetaC n < 45 ↔ √2 < n := by
  have hn0 : 0 < n := by linarith
  unfold thetaC
  have e : arcsin (1 / n) * (180 / π) < 45 ↔ arcsin (1 / n) < π / 4 := by
    rw [← lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> [skip; skip] <;> (convert h using 1; field_simp; ring)
  rw [e, ← not_le, pi_div_four_le_arcsin, not_le]
  have hs : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  rw [div_lt_div_iff₀ hn0 (by norm_num)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- (4) n > 1 で、窓が開く ⇔ n > √2。 -/
theorem opens_iff {n : ℝ} (hn : 1 < n) : (window (thetaC n)).Nonempty ↔ √2 < n := by
  rw [nonempty_iff (thetaC_pos (by linarith)), thetaC_lt_45_iff hn.le]

theorem sin_pi_div_seven_pos : 0 < sin (π / 7) :=
  sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])

/-- 最も広い屈折率 n* = 1/sin(π/7)。 -/
noncomputable def nStar : ℝ := 1 / sin (π / 7)

theorem one_le_nStar : 1 ≤ nStar := by
  unfold nStar
  rw [le_div_iff₀ sin_pi_div_seven_pos, one_mul]
  exact sin_le_one _

/-- (4) θ_c(n) = 180/7 ⇔ n = 1/sin(π/7)。 -/
theorem thetaC_eq_iff {n : ℝ} (hn : 0 < n) : thetaC n = 180 / 7 ↔ n = nStar := by
  unfold thetaC nStar
  have e : arcsin (1 / n) * (180 / π) = 180 / 7 ↔ arcsin (1 / n) = π / 7 := by
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; rw [h]; field_simp
  rw [e, arcsin_eq_iff_eq_sin ⟨by linarith [pi_pos], by linarith [pi_pos]⟩]
  have hs := sin_pi_div_seven_pos
  constructor
  · intro h; rw [← h]; field_simp
  · intro h; rw [h]; field_simp

/-- (4) 幅は 90/7 度以下で、等号は n = 1/sin(π/7) だけ。 -/
theorem width_n_le (n : ℝ) : width (thetaC n) ≤ 90 / 7 := width_le _

theorem width_n_eq_max_iff {n : ℝ} (hn : 0 < n) : width (thetaC n) = 90 / 7 ↔ n = nStar := by
  rw [width_eq_max_iff, thetaC_eq_iff hn]

theorem thetaC_nStar : thetaC nStar = 180 / 7 :=
  (thetaC_eq_iff (lt_of_lt_of_le one_pos one_le_nStar)).mpr rfl

/-- (4) n ≥ 1/sin(π/7) で幅は狭義に減る。 -/
theorem width_n_strictAntiOn : StrictAntiOn (fun n => width (thetaC n)) (Ici nStar) := by
  intro x hx y hy hxy
  rw [mem_Ici] at hx hy
  have h1 : 1 ≤ x := one_le_nStar.trans hx
  have h2 : 1 ≤ y := one_le_nStar.trans hy
  have hθ := thetaC_strictAntiOn (mem_Ici.mpr h1) (mem_Ici.mpr h2) hxy
  have hxle : thetaC x ≤ 180 / 7 := by
    rw [← thetaC_nStar]
    rcases eq_or_lt_of_le hx with he | hlt
    · rw [he]
    · exact (thetaC_strictAntiOn (mem_Ici.mpr one_le_nStar) (mem_Ici.mpr h1) hlt).le
  exact width_strictMonoOn (mem_Iic.mpr (hθ.le.trans hxle)) (mem_Iic.mpr hxle) hθ

/-- (4) √2 ≤ n ≤ 1/sin(π/7) で幅は狭義に増える。 -/
theorem width_n_strictMonoOn : StrictMonoOn (fun n => width (thetaC n)) (Icc (√2) nStar) := by
  intro x hx y hy hxy
  have hs1 : (1 : ℝ) ≤ √2 := by rw [one_le_sqrt]; norm_num
  have h1 : 1 ≤ x := hs1.trans hx.1
  have h2 : 1 ≤ y := hs1.trans hy.1
  have hθ := thetaC_strictAntiOn (mem_Ici.mpr h1) (mem_Ici.mpr h2) hxy
  have hyge : 180 / 7 ≤ thetaC y := by
    rw [← thetaC_nStar]
    rcases eq_or_lt_of_le hy.2 with he | hlt
    · rw [he]
    · exact (thetaC_strictAntiOn (mem_Ici.mpr h2) (mem_Ici.mpr one_le_nStar) hlt).le
  exact width_strictAntiOn (mem_Ici.mpr hyge) (mem_Ici.mpr (hyge.trans hθ.le)) hθ

/-- 90/7 度はラジアンで π/14。 -/
theorem max_in_radians : (90 / 7 : ℝ) * (π / 180) = π / 14 := by ring

end Paper598

end Yamagishi
