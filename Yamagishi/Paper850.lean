/-
論文850『「長く」と「速く」が取り替えられるのは、体を一つの袋と見るときだけである』の格上げ（一般の形）。

日本語の一文：手前の区画（容積 V1）からだけ流量 K で取り除き、奥の区画（V2）と流量 Q で行き来する
二区画の模型で、はじめの濃度が両区画で等しいとき、積 D = Kt を決めると、取り除く割合 R は K について
狭義に減り、どの K でも (V1/V)(1 − e^(−D/V1)) < R < 1 − e^(−D/V) を満たす（V = V1 + V2）。
English: In the two-compartment model with removal at flow K from the first compartment (volume V1)
and exchange at flow Q with the second (V2), starting from equal concentrations, the fraction
removed at fixed D = Kt is strictly decreasing in K and satisfies
(V1/V)(1 − e^(−D/V1)) < R < 1 − e^(−D/V) for every K (V = V1 + V2).

原稿（850_yamagishi_longer_and_faster_only_in_one_bag/…_jp.tex）は、V1 = 15・V2 = 25・Q = 0.6・D = 48 の
四通り（流量 0.2〜1.6 で 0.654〜0.494）と、一区画では四通りが一致することを数値で示している。
単調性と上下の限界の証明は無い。

ここで証明した言明（V1, V2 > 0、ε = Q/K ≥ 0、累積の量 s = Kt を変数に取る）：
  (1) `solution`：濃度 c1(s)、c2(s) の閉じた形（固有値 λ1 < λ2 は λ² − Sλ + P の根、
      S = (1 + ε)/V1 + ε/V2、P = ε/(V1V2)。芯は `sol_core`）は、V1 c1′ = −c1 + ε(c2 − c1)、
      V2 c2′ = ε(c1 − c2)、c1(0) = c2(0) = 1 を満たす。`time_model`：c(Kt) は時間の式
      V1 dc1/dt = −Kc1 + Q(c2 − c1)、V2 dc2/dt = Q(c1 − c2) を満たす。
      `gap_pos`：s > 0 で c2 − c1 = (e^(−λ1 s) − e^(−λ2 s))/(V1(λ2 − λ1)) > 0（奥のほうが濃い）。
      `amount_deriv`：残る量 A = V1c1 + V2c2 は A′ = −c1。
  (2) `upper_bound`：s > 0 で A(s) > V e^(−s/V)、したがって R < 1 − e^(−D/V)（一区画の値が上限）。
      `lower_bound`：ε > 0、s > 0 で A(s) < V2 + V1 e^(−s/V1)、したがって R > (V1/V)(1 − e^(−D/V1))。
  (3) `amount_strictAnti_eps`：0 ≤ ε₁ < ε₂ なら A(D; ε₂) < A(D; ε₁)（行き来が多いほど多く除かれる）。
      芯は Φ(u) = V1 c1⁽²⁾(D − u)c1⁽¹⁾(u) + V2 c2⁽²⁾(D − u)c2⁽¹⁾(u) の微分が
      (ε₂ − ε₁)·δ⁽²⁾(D − u)·δ⁽¹⁾(u) > 0 になること（δ = c2 − c1。模型が容積の重みで対称だから）。
      `removal_strictAnti_K`：Q > 0、0 < K₁ < K₂ なら R(K₂) < R(K₁)（同じ Kt なら速いほど除去が落ちる）。
  (4) `one_bag`：一区画では R = 1 − e^(−Kt/V) で K と t は積でしか入らない。
足した仮定：二区画の模型の式を定義に置き、解は閉じた形として与えた（解がこれ一つであることは
形式化していない）。はじめの濃度が等しいこと、K と Q が時間で一定、体液の量が一定（原稿と同じ）。
形式化していないもの：K → 0 と K → ∞ で上と下の端に近づくこと（ε = 0 で下の端にちょうど等しいことは
`eps_zero` で示した）、原稿の数（下読みの AI が指摘したとおり、閉じた形では 0.654170766・0.615832850・
0.558641377・0.494254889 で、原稿の値と小数第 5〜6 位で食い違う）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper850

open Real Set

variable {V1 V2 ε : ℝ}

/-- S = (1 + ε)/V1 + ε/V2。 -/
noncomputable def S (V1 V2 ε : ℝ) : ℝ := (1 + ε) / V1 + ε / V2
/-- P = ε/(V1V2)。 -/
noncomputable def P (V1 V2 ε : ℝ) : ℝ := ε / (V1 * V2)
/-- 判別式。 -/
noncomputable def disc (V1 V2 ε : ℝ) : ℝ := S V1 V2 ε ^ 2 - 4 * P V1 V2 ε

theorem disc_pos (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) : 0 < disc V1 V2 ε := by
  have e : disc V1 V2 ε = ((1 + ε) / V1 - ε / V2) ^ 2 + 4 * (ε ^ 2 / (V1 * V2)) := by
    unfold disc S P; field_simp; ring
  rw [e]
  rcases eq_or_lt_of_le he with h0 | h0
  · rw [← h0]; simp; positivity
  · have : 0 < ε ^ 2 / (V1 * V2) := by positivity
    nlinarith [sq_nonneg ((1 + ε) / V1 - ε / V2)]

/-- 遅い根 λ1 と速い根 λ2。 -/
noncomputable def l1 (V1 V2 ε : ℝ) : ℝ := (S V1 V2 ε - √(disc V1 V2 ε)) / 2
noncomputable def l2 (V1 V2 ε : ℝ) : ℝ := (S V1 V2 ε + √(disc V1 V2 ε)) / 2

theorem l1_lt_l2 (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) : l1 V1 V2 ε < l2 V1 V2 ε := by
  have := Real.sqrt_pos.mpr (disc_pos h1 h2 he)
  unfold l1 l2; linarith

theorem vieta_sum (V1 V2 ε : ℝ) : l1 V1 V2 ε + l2 V1 V2 ε = S V1 V2 ε := by
  unfold l1 l2; ring

theorem vieta_prod (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) :
    l1 V1 V2 ε * l2 V1 V2 ε = P V1 V2 ε := by
  have := sq_sqrt (disc_pos h1 h2 he).le
  have hd : disc V1 V2 ε = S V1 V2 ε ^ 2 - 4 * P V1 V2 ε := rfl
  unfold l1 l2
  nlinarith [this, hd]

/-- 手前の区画の濃度 c1(s)。 -/
noncomputable def c1 (V1 V2 ε s : ℝ) : ℝ :=
  ((l2 V1 V2 ε - 1 / V1) * exp (-l1 V1 V2 ε * s) + (1 / V1 - l1 V1 V2 ε) * exp (-l2 V1 V2 ε * s)) /
    (l2 V1 V2 ε - l1 V1 V2 ε)

/-- 奥の区画の濃度 c2(s)。 -/
noncomputable def c2 (V1 V2 ε s : ℝ) : ℝ :=
  (l2 V1 V2 ε * exp (-l1 V1 V2 ε * s) - l1 V1 V2 ε * exp (-l2 V1 V2 ε * s)) /
    (l2 V1 V2 ε - l1 V1 V2 ε)

/-- 解の芯（α = 1/V1、β = ε/V1、γ = ε/V2 と置く）：a + b = α + β + γ、ab = αγ、a ≠ b なら、
c1 = ((b − α)e^(−as) + (α − a)e^(−bs))/(b − a)、c2 = (b e^(−as) − a e^(−bs))/(b − a) は
c1′ = −(α + β)c1 + βc2、c2′ = γ(c1 − c2) を満たす。 -/
theorem sol_core {α β γ a b : ℝ} (hab : a ≠ b) (hS : a + b = α + β + γ) (hP : a * b = α * γ)
    (s : ℝ) :
    HasDerivAt (fun s => ((b - α) * exp (-a * s) + (α - a) * exp (-b * s)) / (b - a))
      (-(α + β) * (((b - α) * exp (-a * s) + (α - a) * exp (-b * s)) / (b - a)) +
        β * ((b * exp (-a * s) - a * exp (-b * s)) / (b - a))) s ∧
    HasDerivAt (fun s => (b * exp (-a * s) - a * exp (-b * s)) / (b - a))
      (γ * ((((b - α) * exp (-a * s) + (α - a) * exp (-b * s)) / (b - a)) -
        (b * exp (-a * s) - a * exp (-b * s)) / (b - a))) s := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have ha : HasDerivAt (fun s => exp (-a * s)) (exp (-a * s) * (-a * 1)) s :=
    ((hasDerivAt_id' s).const_mul (-a)).exp
  have hb : HasDerivAt (fun s => exp (-b * s)) (exp (-b * s) * (-b * 1)) s :=
    ((hasDerivAt_id' s).const_mul (-b)).exp
  constructor
  · have := ((ha.const_mul (b - α)).add (hb.const_mul (α - a))).div_const (b - a)
    refine this.congr_deriv ?_
    generalize exp (-a * s) = Ea
    generalize exp (-b * s) = Eb
    field_simp
    linear_combination (Ea - Eb) * (α * hS - hP)
  · have := ((ha.const_mul b).sub (hb.const_mul a)).div_const (b - a)
    refine this.congr_deriv ?_
    generalize exp (-a * s) = Ea
    generalize exp (-b * s) = Eb
    field_simp
    linear_combination (Eb - Ea) * hP

/-- (1) 閉じた形は模型を満たす。 -/
theorem solution (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) (s : ℝ) :
    c1 V1 V2 ε 0 = 1 ∧ c2 V1 V2 ε 0 = 1 ∧
    HasDerivAt (c1 V1 V2 ε) ((-(1 + ε) * c1 V1 V2 ε s + ε * c2 V1 V2 ε s) / V1) s ∧
    HasDerivAt (c2 V1 V2 ε) (ε * (c1 V1 V2 ε s - c2 V1 V2 ε s) / V2) s := by
  have hlt := l1_lt_l2 h1 h2 he
  have hne : l2 V1 V2 ε - l1 V1 V2 ε ≠ 0 := by linarith
  have hS : l1 V1 V2 ε + l2 V1 V2 ε = 1 / V1 + ε / V1 + ε / V2 := by
    rw [vieta_sum]; unfold S; ring
  have hP : l1 V1 V2 ε * l2 V1 V2 ε = 1 / V1 * (ε / V2) := by
    rw [vieta_prod h1 h2 he]; unfold P; field_simp
  have hc := sol_core (β := ε / V1) (ne_of_lt hlt) hS hP s
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold c1; simp only [mul_zero, exp_zero, mul_one]; rw [div_eq_one_iff_eq hne]; ring
  · unfold c2; simp only [mul_zero, exp_zero, mul_one]; rw [div_eq_one_iff_eq hne]
  · refine hc.1.congr_deriv ?_
    unfold c1 c2
    field_simp
  · refine hc.2.congr_deriv ?_
    unfold c1 c2
    field_simp

/-- 奥と手前の濃度の差。 -/
theorem gap_eq (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) (s : ℝ) :
    c2 V1 V2 ε s - c1 V1 V2 ε s =
      (exp (-l1 V1 V2 ε * s) - exp (-l2 V1 V2 ε * s)) / (V1 * (l2 V1 V2 ε - l1 V1 V2 ε)) := by
  have hlt := l1_lt_l2 h1 h2 he
  have hne : l2 V1 V2 ε - l1 V1 V2 ε ≠ 0 := by linarith
  unfold c1 c2
  field_simp
  ring

/-- (1) s > 0 で奥のほうが濃い。 -/
theorem gap_pos (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) {s : ℝ} (hs : 0 < s) :
    0 < c2 V1 V2 ε s - c1 V1 V2 ε s := by
  rw [gap_eq h1 h2 he]
  have hlt := l1_lt_l2 h1 h2 he
  have : exp (-l2 V1 V2 ε * s) < exp (-l1 V1 V2 ε * s) := exp_lt_exp.mpr (by nlinarith)
  apply div_pos (by linarith) (mul_pos h1 (by linarith))

/-- 残る量 A = V1c1 + V2c2。 -/
noncomputable def amount (V1 V2 ε s : ℝ) : ℝ := V1 * c1 V1 V2 ε s + V2 * c2 V1 V2 ε s

theorem amount_zero (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) :
    amount V1 V2 ε 0 = V1 + V2 := by
  unfold amount; rw [(solution h1 h2 he 0).1, (solution h1 h2 he 0).2.1]; ring

/-- (1) A′ = −c1。 -/
theorem amount_deriv (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) (s : ℝ) :
    HasDerivAt (amount V1 V2 ε) (-c1 V1 V2 ε s) s := by
  obtain ⟨_, _, d1, d2⟩ := solution h1 h2 he s
  have := (d1.const_mul V1).add (d2.const_mul V2)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- (1) 時間の式：c(Kt; Q/K) は V1 dc1/dt = −Kc1 + Q(c2 − c1)、V2 dc2/dt = Q(c1 − c2) を満たす。 -/
theorem time_model {K Q : ℝ} (h1 : 0 < V1) (h2 : 0 < V2) (hK : 0 < K) (hQ : 0 ≤ Q) (t : ℝ) :
    HasDerivAt (fun t => c1 V1 V2 (Q / K) (K * t))
      ((-K * c1 V1 V2 (Q / K) (K * t) + Q * (c2 V1 V2 (Q / K) (K * t) -
        c1 V1 V2 (Q / K) (K * t))) / V1) t ∧
    HasDerivAt (fun t => c2 V1 V2 (Q / K) (K * t))
      (Q * (c1 V1 V2 (Q / K) (K * t) - c2 V1 V2 (Q / K) (K * t)) / V2) t := by
  have he : 0 ≤ Q / K := div_nonneg hQ hK.le
  obtain ⟨_, _, d1, d2⟩ := solution h1 h2 he (K * t)
  have hKt : HasDerivAt (fun t => K * t) K t := by
    simpa using (hasDerivAt_id' t).const_mul K
  constructor
  · refine (d1.comp t hKt).congr_deriv ?_
    field_simp
    ring
  · refine (d2.comp t hKt).congr_deriv ?_
    field_simp

/-! ### 上下の限界 -/

/-- (2) s > 0 で A(s) > V e^(−s/V)。 -/
theorem upper_bound (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 ≤ ε) {s : ℝ} (hs : 0 < s) :
    (V1 + V2) * exp (-s / (V1 + V2)) < amount V1 V2 ε s := by
  set V := V1 + V2 with hV
  have hV0 : 0 < V := by positivity
  set F := fun x => amount V1 V2 ε x * exp (x / V) with hF
  have hd : ∀ x, HasDerivAt F ((amount V1 V2 ε x / V - c1 V1 V2 ε x) * exp (x / V)) x := by
    intro x
    have he' : HasDerivAt (fun x => exp (x / V)) (exp (x / V) * (1 / V)) x := by
      have := ((hasDerivAt_id' x).div_const V).exp
      simpa using this
    refine ((amount_deriv h1 h2 he x).mul he').congr_deriv ?_
    ring
  have hmono : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      apply mul_pos _ (exp_pos _)
      have hg := gap_pos h1 h2 he hx
      unfold amount
      rw [sub_pos, lt_div_iff₀ hV0]
      nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs.le) hs
  simp only [hF, zero_div, exp_zero, mul_one] at this
  rw [amount_zero h1 h2 he] at this
  have hE : exp (-s / V) * exp (s / V) = 1 := by rw [← exp_add]; ring_nf; simp
  have hp := exp_pos (s / V)
  have hp2 := exp_pos (-s / V)
  nlinarith

/-- (2) ε > 0、s > 0 で A(s) < V2 + V1 e^(−s/V1)。 -/
theorem lower_bound (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 < ε) {s : ℝ} (hs : 0 < s) :
    amount V1 V2 ε s < V2 + V1 * exp (-s / V1) := by
  -- まず c1(x) > e^(−x/V1)（x > 0）
  have hc1 : ∀ x, 0 < x → exp (-x / V1) < c1 V1 V2 ε x := by
    intro x hx
    set F := fun y => c1 V1 V2 ε y * exp (y / V1) with hF
    have hd : ∀ y, HasDerivAt F (ε * (c2 V1 V2 ε y - c1 V1 V2 ε y) / V1 * exp (y / V1)) y := by
      intro y
      have he' : HasDerivAt (fun y => exp (y / V1)) (exp (y / V1) * (1 / V1)) y := by
        have := ((hasDerivAt_id' y).div_const V1).exp
        simpa using this
      refine (((solution h1 h2 he.le y).2.2.1).mul he').congr_deriv ?_
      field_simp
      ring
    have hmono : StrictMonoOn F (Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact fun y _ => (hd y).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        rw [(hd y).deriv]
        have := gap_pos h1 h2 he.le hy
        positivity
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
    simp only [hF, zero_div, exp_zero, mul_one] at this
    rw [(solution h1 h2 he.le 0).1] at this
    have hE : exp (-x / V1) * exp (x / V1) = 1 := by rw [← exp_add]; ring_nf; simp
    have hp := exp_pos (x / V1)
    nlinarith
  -- G(x) = A(x) − (V2 + V1 e^(−x/V1)) は狭義に減る
  set G := fun x => amount V1 V2 ε x - (V2 + V1 * exp (-x / V1)) with hG
  have hd : ∀ x, HasDerivAt G (-c1 V1 V2 ε x + exp (-x / V1)) x := by
    intro x
    have he' : HasDerivAt (fun x => exp (-x / V1)) (exp (-x / V1) * (-1 / V1)) x := by
      have := ((hasDerivAt_neg x).div_const V1).exp
      simpa [neg_div] using this
    refine ((amount_deriv h1 h2 he.le x).sub ((he'.const_mul V1).const_add V2)).congr_deriv ?_
    field_simp
    ring
  have hanti : StrictAntiOn G (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      linarith [hc1 x hx]
  have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs.le) hs
  simp only [hG, neg_zero, zero_div, exp_zero, mul_one] at this
  rw [amount_zero h1 h2 he.le] at this
  linarith

/-- ε = 0（行き来が無い）では A(s) = V2 + V1 e^(−s/V1) にちょうど等しい。 -/
theorem eps_zero (h1 : 0 < V1) (s : ℝ) :
    amount V1 V2 0 s = V2 + V1 * exp (-s / V1) := by
  have hd : disc V1 V2 0 = (1 / V1) ^ 2 := by unfold disc S P; ring
  have hs : √(disc V1 V2 0) = 1 / V1 := by rw [hd, sqrt_sq (by positivity)]
  have hl1 : l1 V1 V2 0 = 0 := by unfold l1; rw [hs]; unfold S; ring
  have hl2 : l2 V1 V2 0 = 1 / V1 := by unfold l2; rw [hs]; unfold S; ring
  unfold amount c1 c2
  rw [hl1, hl2]
  simp only [neg_zero, zero_mul, exp_zero, mul_one, sub_zero]
  field_simp
  ring_nf

/-- 取り除く割合 R = 1 − A(D)/V。 -/
noncomputable def removal (V1 V2 ε D : ℝ) : ℝ := 1 - amount V1 V2 ε D / (V1 + V2)

/-- (2) 上下の限界：(V1/V)(1 − e^(−D/V1)) < R < 1 − e^(−D/V)（ε > 0、D > 0）。 -/
theorem removal_bounds (h1 : 0 < V1) (h2 : 0 < V2) (he : 0 < ε) {D : ℝ} (hD : 0 < D) :
    V1 / (V1 + V2) * (1 - exp (-D / V1)) < removal V1 V2 ε D ∧
      removal V1 V2 ε D < 1 - exp (-D / (V1 + V2)) := by
  have hV : 0 < V1 + V2 := by positivity
  have hu := upper_bound h1 h2 he.le hD
  have hl := lower_bound h1 h2 he hD
  unfold removal
  constructor
  · rw [show V1 / (V1 + V2) * (1 - exp (-D / V1)) = 1 - (V2 + V1 * exp (-D / V1)) / (V1 + V2) by
      field_simp; ring]
    have := div_lt_div_of_pos_right hl hV
    linarith
  · have : exp (-D / (V1 + V2)) < amount V1 V2 ε D / (V1 + V2) := by
      rw [lt_div_iff₀ hV]; linarith
    linarith

/-! ### 流量についての単調性 -/

/-- (3) 0 ≤ ε₁ < ε₂、D > 0 なら A(D; ε₂) < A(D; ε₁)。 -/
theorem amount_strictAnti_eps {e1 e2 D : ℝ} (h1 : 0 < V1) (h2 : 0 < V2) (he1 : 0 ≤ e1)
    (he : e1 < e2) (hD : 0 < D) : amount V1 V2 e2 D < amount V1 V2 e1 D := by
  have he2 : 0 ≤ e2 := he1.trans he.le
  set Φ := fun u => V1 * c1 V1 V2 e2 (D - u) * c1 V1 V2 e1 u +
    V2 * c2 V1 V2 e2 (D - u) * c2 V1 V2 e1 u with hΦ
  have hd : ∀ u, HasDerivAt Φ ((e2 - e1) * (c2 V1 V2 e2 (D - u) - c1 V1 V2 e2 (D - u)) *
      (c2 V1 V2 e1 u - c1 V1 V2 e1 u)) u := by
    intro u
    obtain ⟨_, _, x1, x2⟩ := solution h1 h2 he1 u
    obtain ⟨_, _, y1, y2⟩ := solution h1 h2 he2 (D - u)
    have hDu : HasDerivAt (fun u => D - u) (-1) u := by
      simpa using (hasDerivAt_id' u).const_sub D
    have y1' := y1.comp u hDu
    have y2' := y2.comp u hDu
    have := ((y1'.const_mul V1).mul x1).add ((y2'.const_mul V2).mul x2)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall
      fun v => by simp only [hΦ, Function.comp, Pi.add_apply, Pi.mul_apply])
    simp only [Function.comp]
    field_simp
    ring
  have hmono : StrictMonoOn Φ (Icc 0 D) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 D)
    · exact fun u _ => (hd u).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u).deriv]
      have g1 := gap_pos h1 h2 he1 hu.1
      have g2 := gap_pos h1 h2 he2 (show 0 < D - u by linarith [hu.2])
      have : 0 < e2 - e1 := by linarith
      positivity
  have := hmono (left_mem_Icc.mpr hD.le) (right_mem_Icc.mpr hD.le) hD
  simp only [hΦ, sub_zero, sub_self] at this
  rw [(solution h1 h2 he1 0).1, (solution h1 h2 he1 0).2.1, (solution h1 h2 he2 0).1,
    (solution h1 h2 he2 0).2.1] at this
  unfold amount
  linarith

/-- (3) Q > 0、0 < K₁ < K₂ なら R(K₂) < R(K₁)（D = Kt を決めて）。 -/
theorem removal_strictAnti_K {Q K1 K2 D : ℝ} (h1 : 0 < V1) (h2 : 0 < V2) (hQ : 0 < Q)
    (hK1 : 0 < K1) (hK : K1 < K2) (hD : 0 < D) :
    removal V1 V2 (Q / K2) D < removal V1 V2 (Q / K1) D := by
  have hlt : Q / K2 < Q / K1 := div_lt_div_of_pos_left hQ hK1 hK
  have := amount_strictAnti_eps h1 h2 (div_nonneg hQ.le (hK1.trans hK).le) hlt hD (V1 := V1)
  unfold removal
  have hV : 0 < V1 + V2 := by positivity
  have := div_lt_div_of_pos_right this hV
  linarith

/-- (4) 一区画では R = 1 − e^(−Kt/V)：K と t は積でしか入らない。 -/
theorem one_bag {V K t K' t' : ℝ} (h : K * t = K' * t') :
    1 - exp (-(K * t) / V) = 1 - exp (-(K' * t') / V) := by rw [h]

end Paper850

end Yamagishi
