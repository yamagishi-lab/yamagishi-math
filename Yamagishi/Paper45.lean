/-
論文45『面積は、立体角ではない』（第 3 版）の格上げ（一般の形）。

原稿（45_yamagishi_strong_cp_hopf_zero_init/…_jp.tex）は、ホップ束 S¹ → S³_R → S²_{R/2} について
4π(R/2)²·2πR = πR²·2πR = 2π²R³ = Vol(S³_R) が任意の R で成り立つことを記号計算で確かめ、
「R = 2 が唯一」は面積と周長を等置した単位の選択であること（R = λR′ で R′ = 2/λ）を示している。
次元は n = 2（S³）だけ。

ここで証明した言明（k 次元球面の体積 Vol(S^k_r) = 2π^((k+1)/2) r^k / Γ((k+1)/2) を定義として置く）：
  (1) `vol_one`・`vol_two`・`vol_three`：Vol(S¹_r) = 2πr、Vol(S²_r) = 4πr²、Vol(S³_r) = 2π²r³。
      `paper_hopf`：4π(R/2)²·2πR = 2π²R³（原稿の式）。
  (2) `hopf_factor`：すべての実数 n > 0 と R > 0 で Vol(S^{2n−1}_R) = Vol(S^n_{R/2})·Vol(S^{n−1}_R)
      （ルジャンドルの倍数公式 Γ(s)Γ(s + 1/2) = Γ(2s)2^(1−2s)√π、Mathlib の `Real.Gamma_mul_Gamma_add_half`）。
  (3) `strictConvexOn_log_Gamma`：log Γ は (0, ∞) で狭義に凸（Mathlib には凸までしか無いので、
      関数等式 Γ(x + 1) = xΓ(x) と log の狭義の凹性から導いた）。
      `gamma_ratio_strictMonoOn`：a > 0 なら x ↦ Γ(x + a)/Γ(x) は (0, ∞) で狭義に増える。
  (4) `hopf_unique_m`：n > 0 を固定すると、実数 m > −1 で Vol(S^{n+m}_R) = Vol(S^n_{R/2})·Vol(S^m_R)
      となるのは m = n − 1 のときだけ。
      `hopf_unique_scale`：m = n − 1 のとき、底の半径を cR（c > 0）にして等号になるのは c = 1/2 だけ。
  (5) `unit_choice`：面積 π(λR′)² と周長 2π(λR′) が等しい ⇔ R′ = 2/λ（λ > 0）。
足した所：次元 n を一般の正の実数に上げたこと、一意性の二つ（m と底の半径の比）。
形式化していないもの：Vol の式が球面の測度に等しいこと（定義として置いた）、束として実現するのが
n = 1, 2, 4, 8 だけというアダムスの定理、チャーン類・インスタントン・強い CP 問題の物理。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）

For every real n > 0 and every radius R, Vol(S^{2n−1}_R) = Vol(S^n_{R/2})·Vol(S^{n−1}_R), and for
fixed n the factorisation Vol(S^{n+m}_R) = Vol(S^n_{R/2})·Vol(S^m_R) holds only at m = n − 1; the
proof uses Legendre's duplication formula and the strict log-convexity of Γ.
-/
import Mathlib

namespace Yamagishi

namespace Paper45

open Real Set

/-- k 次元球面（ℝ^(k+1) の中）の半径 r の体積。 -/
noncomputable def vol (k r : ℝ) : ℝ := 2 * π ^ ((k + 1) / 2) * r ^ k / Gamma ((k + 1) / 2)

/-- (1) Vol(S¹_r) = 2πr。 -/
theorem vol_one (r : ℝ) : vol 1 r = 2 * π * r := by
  unfold vol; norm_num

/-- (1) Vol(S²_r) = 4πr²。 -/
theorem vol_two (r : ℝ) : vol 2 r = 4 * π * r ^ 2 := by
  unfold vol
  have h1 : (2 + 1 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h1, Gamma_add_one (by norm_num), Gamma_one_half_eq, rpow_add pi_pos, rpow_one,
    ← sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  have hs : 0 < √π := sqrt_pos.mpr pi_pos
  field_simp
  ring

/-- (1) Vol(S³_r) = 2π²r³。 -/
theorem vol_three (r : ℝ) : vol 3 r = 2 * π ^ 2 * r ^ 3 := by
  unfold vol
  rw [show (3 + 1 : ℝ) / 2 = 2 by norm_num, Gamma_two,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast]
  norm_num

/-- (1) 原稿の式：4π(R/2)²·2πR = 2π²R³。 -/
theorem paper_hopf (R : ℝ) : vol 2 (R / 2) * vol 1 R = vol 3 R := by
  rw [vol_two, vol_one, vol_three]; ring

/-- (2) ホップの因子分解：すべての n > 0、R > 0 で Vol(S^{2n−1}_R) = Vol(S^n_{R/2})·Vol(S^{n−1}_R)。 -/
theorem hopf_factor {n R : ℝ} (hn : 0 < n) (hR : 0 < R) :
    vol (2 * n - 1) R = vol n (R / 2) * vol (n - 1) R := by
  unfold vol
  have hL := Gamma_mul_Gamma_add_half (n / 2)
  rw [show 2 * (n / 2) = n by ring] at hL
  rw [show (2 * n - 1 + 1) / 2 = n by ring, show (n - 1 + 1) / 2 = n / 2 by ring,
    show (n + 1) / 2 = n / 2 + 1 / 2 by ring]
  have hp := pi_pos
  have hG1 : 0 < Gamma n := Gamma_pos_of_pos hn
  have hGa : 0 < Gamma (n / 2) := Gamma_pos_of_pos (by linarith)
  have hGb : 0 < Gamma (n / 2 + 1 / 2) := Gamma_pos_of_pos (by linarith)
  -- 冪を原子に分ける
  have e1 : π ^ n = π ^ (n / 2) * π ^ (n / 2) := by rw [← rpow_add hp]; ring_nf
  have e2 : π ^ (n / 2 + 1 / 2) = π ^ (n / 2) * √π := by rw [rpow_add hp, sqrt_eq_rpow]
  have e3 : R ^ (2 * n - 1) = R ^ n * R ^ n / R := by
    rw [rpow_sub hR, rpow_one, ← rpow_add hR]; ring_nf
  have e4 : R ^ (n - 1) = R ^ n / R := by rw [rpow_sub hR, rpow_one]
  have e5 : (R / 2) ^ n = R ^ n / 2 ^ n := div_rpow hR.le (by norm_num) n
  have e6 : (2 : ℝ) ^ (1 - n) = 2 / 2 ^ n := by rw [rpow_sub (by norm_num), rpow_one]
  rw [e6] at hL
  rw [e1, e2, e3, e4, e5]
  have h2n : 0 < (2 : ℝ) ^ n := rpow_pos_of_pos (by norm_num) n
  have hs : 0 < √π := sqrt_pos.mpr hp
  rw [div_mul_div_comm, div_eq_div_iff hG1.ne' (mul_pos hGb hGa).ne']
  have hL' : Gamma (n / 2 + 1 / 2) * Gamma (n / 2) = Gamma n * (2 / 2 ^ n) * √π := by
    rw [mul_comm]; exact hL
  rw [hL']
  field_simp

/-- log Γ(x + 1) = log Γ(x) + log x（x > 0）。 -/
theorem log_Gamma_succ {x : ℝ} (hx : 0 < x) :
    log (Gamma (x + 1)) = log (Gamma x) + log x := by
  rw [Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]

/-- (3) log Γ は (0, ∞) で狭義に凸。 -/
theorem strictConvexOn_log_Gamma : StrictConvexOn ℝ (Ioi 0) (log ∘ Gamma) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  simp only [Function.comp, smul_eq_mul]
  set z := a * x + b * y with hz
  have hz0 : 0 < z := by positivity
  -- 凸性を x + 1, y + 1 に使う
  have hc := convexOn_log_Gamma.2 (show x + 1 ∈ Ioi (0 : ℝ) from by simp; linarith)
    (show y + 1 ∈ Ioi (0 : ℝ) from by simp; linarith) ha.le hb.le hab
  simp only [Function.comp, smul_eq_mul] at hc
  have hz1 : a * (x + 1) + b * (y + 1) = z + 1 := by rw [hz]; linear_combination hab
  rw [hz1] at hc
  -- log の狭義の凹性
  have hlog := strictConcaveOn_log_Ioi.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hlog
  rw [← hz] at hlog
  rw [log_Gamma_succ hz0, log_Gamma_succ hx', log_Gamma_succ hy'] at hc
  nlinarith

/-- 狭義に凸な f と a > 0 について、x ↦ f(x + a) − f(x) は狭義に増える。 -/
theorem shift_diff_strictMono {f : ℝ → ℝ} (hf : StrictConvexOn ℝ (Ioi 0) f) {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun x => f (x + a) - f x) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  simp only
  have m1 : x + a ∈ Ioi (0 : ℝ) := by simp; linarith
  have m2 : y + a ∈ Ioi (0 : ℝ) := by simp; linarith
  -- 傾き (x, x + a) < 傾き (x, y + a)
  have s1 := hf.secant_strict_mono hx m1 m2 (by linarith) (by linarith) (by linarith)
  -- 傾き (y + a, x) < 傾き (y + a, y)
  have s2 := hf.secant_strict_mono m2 hx hy (by linarith) (by linarith) hxy
  have e1 : (f x - f (y + a)) / (x - (y + a)) = (f (y + a) - f x) / (y + a - x) := by
    rw [← neg_div_neg_eq]; ring_nf
  have e2 : (f y - f (y + a)) / (y - (y + a)) = (f (y + a) - f y) / a := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [e1, e2] at s2
  rw [show x + a - x = a by ring] at s1
  have := s1.trans s2
  have := mul_lt_mul_of_pos_right this ha
  rwa [div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ ha.ne'] at this

/-- (3) a > 0 なら x ↦ Γ(x + a)/Γ(x) は (0, ∞) で狭義に増える。 -/
theorem gamma_ratio_strictMonoOn {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun x => Gamma (x + a) / Gamma x) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have h := shift_diff_strictMono strictConvexOn_log_Gamma ha hx hy hxy
  simp only [Function.comp] at h
  simp only
  have p1 := Gamma_pos_of_pos (show 0 < x + a by linarith)
  have p2 := Gamma_pos_of_pos hx'
  have p3 := Gamma_pos_of_pos (show 0 < y + a by linarith)
  have p4 := Gamma_pos_of_pos hy'
  rw [← log_div p1.ne' p2.ne', ← log_div p3.ne' p4.ne'] at h
  exact (log_lt_log_iff (div_pos p1 p2) (div_pos p3 p4)).mp h

/-- 体積の比を Γ の比で書く：Vol(S^{n+m}_R) = Vol(S^n_{R/2})·Vol(S^m_R) ⇔
Γ(x + a)/Γ(x) = Γ(a + 1/2)·2^(n−1)/√π（a = n/2、x = (m + 1)/2）。 -/
theorem factor_iff {n m R : ℝ} (hn : 0 < n) (hm : -1 < m) (hR : 0 < R) :
    vol (n + m) R = vol n (R / 2) * vol m R ↔
      Gamma ((m + 1) / 2 + n / 2) / Gamma ((m + 1) / 2) =
        Gamma (n / 2 + 1 / 2) * (2 ^ n / 2) / √π := by
  unfold vol
  have hp := pi_pos
  set x := (m + 1) / 2 with hxdef
  have hx : 0 < x := by rw [hxdef]; linarith
  rw [show (n + m + 1) / 2 = x + n / 2 by rw [hxdef]; ring,
    show (n + 1) / 2 = n / 2 + 1 / 2 by ring]
  have hGx : 0 < Gamma x := Gamma_pos_of_pos hx
  have hGxa : 0 < Gamma (x + n / 2) := Gamma_pos_of_pos (by linarith)
  have hGb : 0 < Gamma (n / 2 + 1 / 2) := Gamma_pos_of_pos (by linarith)
  have e1 : π ^ (x + n / 2) = π ^ x * π ^ (n / 2) := rpow_add hp _ _
  have e2 : π ^ (n / 2 + 1 / 2) = π ^ (n / 2) * √π := by rw [rpow_add hp, sqrt_eq_rpow]
  have e3 : R ^ (n + m) = R ^ n * R ^ m := rpow_add hR _ _
  have e5 : (R / 2) ^ n = R ^ n / 2 ^ n := div_rpow hR.le (by norm_num) n
  rw [e1, e2, e3, e5]
  have h2n : 0 < (2 : ℝ) ^ n := rpow_pos_of_pos (by norm_num) n
  have hs : 0 < √π := sqrt_pos.mpr hp
  have hA : 0 < π ^ x := rpow_pos_of_pos hp _
  have hB : 0 < π ^ (n / 2) := rpow_pos_of_pos hp _
  have hRn : 0 < R ^ n := rpow_pos_of_pos hR _
  have hRm : 0 < R ^ m := rpow_pos_of_pos hR _
  set C := 2 * (π ^ x * π ^ (n / 2)) * (R ^ n * R ^ m) with hC
  have hC0 : 0 < C := by positivity
  have hl : 2 * (π ^ x * π ^ (n / 2)) * (R ^ n * R ^ m) / Gamma (x + n / 2) =
      C * (1 / Gamma (x + n / 2)) := by rw [hC]; ring
  have hr : 2 * (π ^ (n / 2) * √π) * (R ^ n / 2 ^ n) / Gamma (n / 2 + 1 / 2) *
      (2 * π ^ x * R ^ m / Gamma x) =
      C * (2 * √π / (2 ^ n * Gamma (n / 2 + 1 / 2) * Gamma x)) := by
    rw [hC]; field_simp
  rw [hl, hr, mul_right_inj' hC0.ne', div_eq_div_iff hGxa.ne' (by positivity),
    div_eq_div_iff hGx.ne' hs.ne']
  constructor <;> intro h <;> linarith

/-- (4) n > 0 を固定すると、m > −1 で Vol(S^{n+m}_R) = Vol(S^n_{R/2})·Vol(S^m_R) ⇔ m = n − 1。 -/
theorem hopf_unique_m {n m R : ℝ} (hn : 0 < n) (hm : -1 < m) (hR : 0 < R) :
    vol (n + m) R = vol n (R / 2) * vol m R ↔ m = n - 1 := by
  have hm1 : -1 < n - 1 := by linarith
  have h0 := hopf_factor hn hR
  rw [show 2 * n - 1 = n + (n - 1) by ring] at h0
  have hK := (factor_iff hn hm1 hR).mp h0
  rw [factor_iff hn hm hR, ← hK]
  have hx : (m + 1) / 2 ∈ Ioi (0 : ℝ) := by simp; linarith
  have ha : (n - 1 + 1) / 2 ∈ Ioi (0 : ℝ) := by simp; linarith
  constructor
  · intro h
    have := (gamma_ratio_strictMonoOn (show 0 < n / 2 by linarith)).injOn hx ha h
    linarith
  · intro h; rw [h]

/-- (4) m = n − 1 のとき、底の半径を cR（c > 0）にして等号になるのは c = 1/2 だけ。 -/
theorem hopf_unique_scale {n R c : ℝ} (hn : 0 < n) (hR : 0 < R) (hc : 0 < c) :
    vol (2 * n - 1) R = vol n (c * R) * vol (n - 1) R ↔ c = 1 / 2 := by
  rw [hopf_factor hn hR]
  have hpos : 0 < vol (n - 1) R := by
    unfold vol
    have := Gamma_pos_of_pos (show 0 < (n - 1 + 1) / 2 by linarith)
    have := rpow_pos_of_pos pi_pos ((n - 1 + 1) / 2)
    have := rpow_pos_of_pos hR (n - 1)
    positivity
  rw [mul_left_inj' hpos.ne']
  have hK : ∀ r, vol n r = (2 * π ^ ((n + 1) / 2) / Gamma ((n + 1) / 2)) * r ^ n := by
    intro r; unfold vol; ring
  have hK0 : 0 < 2 * π ^ ((n + 1) / 2) / Gamma ((n + 1) / 2) := by
    have := Gamma_pos_of_pos (show 0 < (n + 1) / 2 by linarith)
    have := rpow_pos_of_pos pi_pos ((n + 1) / 2)
    positivity
  rw [hK, hK, mul_right_inj' hK0.ne']
  constructor
  · intro h
    rcases lt_trichotomy (c * R) (R / 2) with h1 | h1 | h1
    · have := rpow_lt_rpow (by positivity) h1 hn; linarith
    · field_simp at h1; linarith
    · have := rpow_lt_rpow (by positivity) h1 hn; linarith
  · intro h; rw [h]; ring_nf

/-- (5) 面積 π(λR′)² と周長 2π(λR′) が等しい ⇔ R′ = 2/λ（目盛りを λ 倍に変えた半径）。 -/
theorem unit_choice {lam R' : ℝ} (hl : 0 < lam) (hR : 0 < R') :
    π * (lam * R') ^ 2 = 2 * π * (lam * R') ↔ R' = 2 / lam := by
  have hp := pi_pos
  rw [eq_div_iff hl.ne']
  constructor
  · intro h
    have : π * (lam * R') * (lam * R' - 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · have : 0 < π * (lam * R') := by positivity
      linarith
    · linarith
  · intro h
    rw [show lam * R' = 2 by linarith]; ring

end Paper45

end Yamagishi
