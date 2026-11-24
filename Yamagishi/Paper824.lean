/-
論文824『核の大きさは P 波の影が決め、核が液体であることは S 波の不在が決める』の格上げ（芯だけ）。

日本語の一文：かすめる射線の震央距離を射線の積分の式で書いたものを入力に置くと、マントルの P 波の速さが
連続で、どの半径でも核の縁の真上の速さを超えないなら、その距離は直進の角 2 arccos(r_c/R) 以下で、
等号はマントルの速さが一定のときだけであり、直進と置いて出す核の半径 R cos(Δ/2) はいつも真の半径以上に
なる。ずれ弾性率が 0 のときだけ S 波の速さがちょうど 0 になる。
English: Core only: with the ray-integral formula for the grazing ray taken as input (from the
general statement of Paper 688), if the mantle P speed is continuous and nowhere exceeds the speed
just above the core, the grazing distance is at most 2 arccos(r_c/R), with equality only for a
constant mantle speed, so the straight-ray radius R cos(Δ/2) is never below the true core radius;
the S speed √(μ/ρ) vanishes exactly when μ = 0.

原稿（824_yamagishi_size_from_the_shadow_state_from_the_missing_shear_wave/…_jp.tex）は、影の始まり
103 度から直進と置いた核の半径 3966.0 km（実際の 1.139667 倍）と、実際の核から出る角 113.783157 度を
出し、観察 2.2 で「まっすぐ進むと置くと核は大きく出る（深いほど速いので）」と言葉で述べている。
芯の観察 3.2 は μ = 0 で S 波の速さがちょうど 0 になること。一般の証明は無い。

ここで証明した言明（0 < r_c < R、v は [r_c, R] で連続で正、どの r ∈ [r_c, R] でも v(r) ≤ v(r_c)）：
  (1) `grazing_le_straight`：Δ ≤ 2 arccos(r_c/R)。
  (2) `grazing_eq_iff_const`：等号 ⇔ [r_c, R] のすべての r で v(r) = v(r_c)（マントルの速さが一定）。
  (3) `core_overestimated`：R cos(Δ/2) ≥ r_c。速さが一定でなければ R cos(Δ/2) > r_c（核を大きく見積もる）。
  (4) `shear_speed_zero_iff`：ρ > 0、μ ≥ 0 で √(μ/ρ) = 0 ⇔ μ = 0。`pressure_speed_pos`：K > 0 なら
      μ = 0 でも P 波の速さ √((K + 4μ/3)/ρ) は正。
論文688 との関係：688 の言明（(r_c, R] で v ≤ v_c、等号はほとんど至る所で v = v_c のとき）と、824 の
言明（[r_c, R] で v ≤ v_c、等号は一定のとき）は、射線の式と仮定が同じで、ちがいは等号の言い方だけである。
速さが連続なら「ほとんど至る所で一定」と「一定」は同じなので、ここでは 688 の定理を読み込んで、連続の
仮定を足して導いた（`Yamagishi/Paper688.lean` の `grazing_le`・`grazing_eq_iff`・`radius_gt`）。
足した仮定（ここが「芯だけ」の理由）：688 と同じく、かすめる射線の震央距離を射線の積分の式として定義に
置いた（`Paper688.Delta`）。観測の影の始まりがかすめる射線と一致すること（三重化が無いこと、回折を
入れないこと）と、速さの式 v_P、v_S の導き方は形式化していない。等号の言い方のために、速さの分布の
連続を足した（段のある構造では「ほとんど至る所」の形の 688 の定理を使う）。
形式化していないもの：原稿の数（3966.0 km・1.139667・計算 3.1 の表）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Yamagishi.Paper688

namespace Yamagishi

namespace Paper824

open Real Set MeasureTheory Paper688

/-- 連続な速さの分布は (r_c, R] で測れる。 -/
theorem aemeasurable_of_continuousOn {v : ℝ → ℝ} {rc R : ℝ}
    (hcont : ContinuousOn v (Icc rc R)) : AEMeasurable v (volume.restrict (Ioc rc R)) :=
  (hcont.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc

/-- (1) Δ ≤ 2 arccos(r_c/R)。 -/
theorem grazing_le_straight {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hcont : ContinuousOn v (Icc rc R)) (hpos : ∀ r ∈ Icc rc R, 0 < v r)
    (hle : ∀ r ∈ Icc rc R, v r ≤ v rc) :
    Delta v rc R ≤ 2 * arccos (rc / R) :=
  grazing_le hrc hR (aemeasurable_of_continuousOn hcont)
    (fun r hr => hpos r (Ioc_subset_Icc_self hr)) (hpos rc ⟨le_rfl, hR.le⟩)
    (fun r hr => hle r (Ioc_subset_Icc_self hr))

/-- (2) 等号 ⇔ マントルの速さが一定。 -/
theorem grazing_eq_iff_const {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hcont : ContinuousOn v (Icc rc R)) (hpos : ∀ r ∈ Icc rc R, 0 < v r)
    (hle : ∀ r ∈ Icc rc R, v r ≤ v rc) :
    Delta v rc R = 2 * arccos (rc / R) ↔ ∀ r ∈ Icc rc R, v r = v rc := by
  rw [grazing_eq_iff hrc hR (aemeasurable_of_continuousOn hcont)
    (fun r hr => hpos r (Ioc_subset_Icc_self hr)) (hpos rc ⟨le_rfl, hR.le⟩)
    (fun r hr => hle r (Ioc_subset_Icc_self hr))]
  constructor
  · intro h r hr
    rcases eq_or_lt_of_le hr.1 with h0 | h0
    · rw [h0]
    · have heq : EqOn v (fun _ => v rc) (Ioc rc R) :=
        Measure.eqOn_Ioc_of_ae_eq volume h (hcont.mono Ioc_subset_Icc_self) continuousOn_const
      exact heq ⟨h0, hr.2⟩
  · intro h
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact h r (Ioc_subset_Icc_self hr)

/-- (3) 直進と置いた核の半径は真の半径以上で、速さが一定でなければ真に大きい。 -/
theorem core_overestimated {v : ℝ → ℝ} {rc R : ℝ} (hrc : 0 < rc) (hR : rc < R)
    (hcont : ContinuousOn v (Icc rc R)) (hpos : ∀ r ∈ Icc rc R, 0 < v r)
    (hle : ∀ r ∈ Icc rc R, v r ≤ v rc) :
    rc ≤ R * cos (Delta v rc R / 2) ∧
      ((∃ r ∈ Icc rc R, v r ≠ v rc) → rc < R * cos (Delta v rc R / 2)) := by
  have hm := aemeasurable_of_continuousOn hcont
  have hp : ∀ r ∈ Ioc rc R, 0 < v r := fun r hr => hpos r (Ioc_subset_Icc_self hr)
  have hvc : 0 < v rc := hpos rc ⟨le_rfl, hR.le⟩
  have hl : ∀ r ∈ Ioc rc R, v r ≤ v rc := fun r hr => hle r (Ioc_subset_Icc_self hr)
  refine ⟨radius_ge hrc hR hm hp hvc hl, ?_⟩
  rintro ⟨r, hr, hne⟩
  apply (radius_gt hrc hR hm hp hvc hl _).2
  intro hae
  have hiff := grazing_eq_iff_const hrc hR hcont hpos hle
  have : Delta v rc R = 2 * arccos (rc / R) := (grazing_eq_iff hrc hR hm hp hvc hl).mpr hae
  exact hne (hiff.mp this r hr)

/-- (4) S 波の速さ √(μ/ρ) が 0 ⇔ μ = 0。 -/
theorem shear_speed_zero_iff {μ ρ : ℝ} (hρ : 0 < ρ) (hμ : 0 ≤ μ) : √(μ / ρ) = 0 ↔ μ = 0 := by
  rw [sqrt_eq_zero (div_nonneg hμ hρ.le), div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (ne_of_gt hρ)
  · intro h; exact Or.inl h

/-- (4) K > 0 なら、μ = 0 でも P 波の速さは正。 -/
theorem pressure_speed_pos {K μ ρ : ℝ} (hK : 0 < K) (hμ : 0 ≤ μ) (hρ : 0 < ρ) :
    0 < √((K + 4 / 3 * μ) / ρ) :=
  sqrt_pos.mpr (div_pos (by linarith) hρ)

end Paper824

end Yamagishi
