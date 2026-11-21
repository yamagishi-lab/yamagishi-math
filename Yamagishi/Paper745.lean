/-
論文745『深さの値打ちは 0 か指数か』の言明を、一般の深さ L で機械に確かめさせる（格上げ）。

原稿（745_yamagishi_depth_is_worth_zero_or_an_exponent/…_jp.tex）が示している事：
  計算 2.1：6×6 の乱数の行列三つで、三層と一層の出力の差が丸めの大きさ（5.192×10⁻¹⁵）。
    |x| の最良の直線近似の平均二乗誤差 0.083342 が 1/12 に合う。|x| = ReLU(x) + ReLU(−x)。
  計算 3.1：テント写像 t(x) = 2ReLU(x) − 4ReLU(x − 1/2) を L 回合成した関数の直線の区間を、
    L = 1, 2, 3, 4, 6, 8, 10 で数え、2^L になる（一層で作るなら 2^L − 1 個の ReLU が要る）。
    理由は「一層ぶんの合成ごとに、区間のそれぞれが二つに折り返される」という一文。

ここで証明した一般の言明：
  (1) 何枚（任意の枚数、任意の大きさ）の線形の層を重ねても、行列の積の一層と同じ（恒等式）。
  (2) |x| = ReLU(x) + ReLU(−x)。
  (3) [−1, 1] の一様な重みで、どの直線 a + bx でも平均二乗誤差は (a − 1/2)² + b²/3 + 1/12 ≥ 1/12、
      等号は a = 1/2、b = 0 のときだけ。
  (4) すべての L について、t を L 回合成した関数は、[0, 1] を 2^L 個の等しい区間
      [k/2^L, (k+1)/2^L] に分けた各区間で傾き ±2^L の一次式（k が偶数なら 2^L x − k、奇数なら k + 1 − 2^L x）。
      格子の点 k/2^L での値は k が偶数なら 0、奇数なら 1（帰納法）。
  (5) 内側の 2^L − 1 個の格子の点では微分できない（左右の傾きが ±2^L で食い違う）。
  (6) 一層（隠れ層一つ）の ReLU の網 c₀ + c₁x + Σ aᵢ ReLU(wᵢx − bᵢ) が [0, 1] で t の L 回合成と
      一致するなら、ReLU の数 N は 2^L − 1 以上（どの ReLU も折れ目を一つしか作らないため）。
足した仮定：(6) の「一層の網」は、一次元の入力、隠れ層一つ、出力は一次の和、として置いた。
「区間の数がちょうど 2^L」は、(4) と (5)（2^L 個の一次の区間があり、隣どうしは傾きの符号が違うので
まとめられない）の形で書いた。区間の数という言葉そのものの定義は置いていない。

形式化していないもの：乱数の行列での数値の確かめ、テルガルスキー（2016）の一般の深さの分離の定理、
「深さの値打ちは連続には増えない」という読み、分離子。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper745

open Set intervalIntegral

/-! ### (1) 線形の層は何枚重ねても一層 -/

/-- 層の並び Ws = [W₁, W₂, …] を、右の層から順に入力に当てる。 -/
def applyLayers {n : ℕ} (Ws : List (Matrix (Fin n) (Fin n) ℝ)) (x : Fin n → ℝ) : Fin n → ℝ :=
  Ws.foldr (fun W v => W.mulVec v) x

/-- (1) 何枚重ねても、行列の積 W₁W₂⋯ の一層と厳密に同じ。 -/
theorem linear_layers_collapse {n : ℕ} (Ws : List (Matrix (Fin n) (Fin n) ℝ)) (x : Fin n → ℝ) :
    applyLayers Ws x = Ws.prod.mulVec x := by
  induction Ws with
  | nil => simp [applyLayers]
  | cons W Ws ih =>
    simp only [applyLayers, List.foldr_cons, List.prod_cons] at ih ⊢
    rw [ih, Matrix.mulVec_mulVec]

/-! ### (2)(3) |x| と最良の直線 -/

noncomputable def relu (x : ℝ) : ℝ := max 0 x

/-- (2) |x| = ReLU(x) + ReLU(−x)。 -/
theorem abs_eq_relu (x : ℝ) : |x| = relu x + relu (-x) := by
  unfold relu
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_left h, max_eq_right (by linarith)]; ring

/-- (3) [−1, 1] の一様な重みでの平均二乗誤差は (a − 1/2)² + b²/3 + 1/12。 -/
theorem mse_line (a b : ℝ) :
    (1 / 2) * ∫ x in (-1 : ℝ)..1, (|x| - a - b * x) ^ 2 = (a - 1 / 2) ^ 2 + b ^ 2 / 3 + 1 / 12 := by
  have hint : ∀ c : ℝ, ∀ u v : ℝ,
      ∫ x in u..v, (c * x - a) ^ 2 =
        (c ^ 2 * v ^ 3 / 3 - a * c * v ^ 2 + a ^ 2 * v) -
          (c ^ 2 * u ^ 3 / 3 - a * c * u ^ 2 + a ^ 2 * u) := by
    intro c u v
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      have := ((((hasDerivAt_pow 3 x).const_mul (c ^ 2 / 3)).sub
        ((hasDerivAt_pow 2 x).const_mul (a * c))).add ((hasDerivAt_id' x).const_mul (a ^ 2)))
      convert this using 1
      · ext y; simp only [Pi.add_apply, Pi.sub_apply]; ring
      · push_cast; ring
    · exact (by fun_prop : Continuous fun x : ℝ => (c * x - a) ^ 2).intervalIntegrable _ _
  have hsplit := integral_add_adjacent_intervals
    (f := fun x : ℝ => (|x| - a - b * x) ^ 2) (a := -1) (b := 0) (c := 1)
    ((by fun_prop : Continuous fun x : ℝ => (|x| - a - b * x) ^ 2).intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((by fun_prop : Continuous fun x : ℝ => (|x| - a - b * x) ^ 2).intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
  have hneg : ∫ x in (-1 : ℝ)..0, (|x| - a - b * x) ^ 2 =
      ∫ x in (-1 : ℝ)..0, ((-1 - b) * x - a) ^ 2 := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simp only
    rw [abs_of_nonpos hx.2]; ring
  have hpos : ∫ x in (0 : ℝ)..1, (|x| - a - b * x) ^ 2 =
      ∫ x in (0 : ℝ)..1, ((1 - b) * x - a) ^ 2 := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simp only
    rw [abs_of_nonneg hx.1]; ring
  rw [← hsplit, hneg, hpos, hint, hint]
  ring

/-- (3) どの直線でも平均二乗誤差は 1/12 以上、等号は a = 1/2、b = 0 のときだけ。 -/
theorem best_line (a b : ℝ) :
    1 / 12 ≤ (1 / 2) * ∫ x in (-1 : ℝ)..1, (|x| - a - b * x) ^ 2 ∧
    ((1 / 2) * ∫ x in (-1 : ℝ)..1, (|x| - a - b * x) ^ 2 = 1 / 12 ↔ a = 1 / 2 ∧ b = 0) := by
  rw [mse_line]
  refine ⟨by nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg b], ?_⟩
  constructor
  · intro h
    have h1 : (a - 1 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg b]
    have h2 : b ^ 2 = 0 := by nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg b]
    exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := a - 1/2) two_ne_zero |>.mp h1],
      pow_eq_zero_iff two_ne_zero |>.mp h2⟩
  · rintro ⟨rfl, rfl⟩; ring

/-! ### (4) テント写像の L 回合成 -/

/-- テント写像 t(x) = 2ReLU(x) − 4ReLU(x − 1/2)。 -/
noncomputable def tent (x : ℝ) : ℝ := 2 * relu x - 4 * relu (x - 1 / 2)

theorem tent_left (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : tent x = 2 * x := by
  unfold tent relu
  rw [max_eq_right h0, max_eq_left (by linarith)]; ring

theorem tent_right (x : ℝ) (h0 : 1 / 2 ≤ x) : tent x = 2 - 2 * x := by
  unfold tent relu
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring

/-- 区間 k の上の一次式（k が偶数なら 2^L x − k、奇数なら k + 1 − 2^L x）。 -/
noncomputable def piece (L k : ℕ) (x : ℝ) : ℝ :=
  if Even k then 2 ^ L * x - k else (k + 1) - 2 ^ L * x

/-- (4) すべての L、すべての k < 2^L、x ∈ [k/2^L, (k+1)/2^L] で、t の L 回合成は piece L k。 -/
theorem tent_iterate (L : ℕ) :
    ∀ k : ℕ, k < 2 ^ L → ∀ x : ℝ, (k : ℝ) / 2 ^ L ≤ x → x ≤ ((k : ℝ) + 1) / 2 ^ L →
      tent^[L] x = piece L k x := by
  induction L with
  | zero =>
    intro k hk x _ _
    have : k = 0 := by simpa using hk
    subst this
    simp [piece]
  | succ L ih =>
    intro k hk x hx1 hx2
    have hP : (0 : ℝ) < 2 ^ L := by positivity
    have hP' : (2 : ℝ) ^ (L + 1) = 2 * 2 ^ L := by ring
    rw [Function.iterate_succ_apply]
    rw [hP'] at hx1 hx2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    by_cases hkL : k < 2 ^ L
    · -- 左半分：t x = 2x
      have hxl : x ≤ 1 / 2 := by
        have : ((k : ℝ) + 1) ≤ 2 ^ L := by exact_mod_cast hkL
        calc x ≤ ((k : ℝ) + 1) / (2 * 2 ^ L) := hx2
          _ ≤ 2 ^ L / (2 * 2 ^ L) := by gcongr
          _ = 1 / 2 := by field_simp
      have hx0 : 0 ≤ x := le_trans (by positivity) hx1
      rw [tent_left x hx0 hxl]
      rw [ih k hkL (2 * x)
        (by rw [div_le_iff₀ hP] at *; rw [div_le_iff₀ (by positivity)] at hx1; linarith)
        (by rw [le_div_iff₀ hP]; rw [le_div_iff₀ (by positivity)] at hx2; linarith)]
      unfold piece
      split_ifs <;> ring
    · -- 右半分：t x = 2 − 2x、区間の番号は k' = 2^(L+1) − 1 − k
      push Not at hkL
      have hxr : 1 / 2 ≤ x := by
        have : (2 : ℝ) ^ L ≤ k := by exact_mod_cast hkL
        calc (1 : ℝ) / 2 = 2 ^ L / (2 * 2 ^ L) := by field_simp
          _ ≤ (k : ℝ) / (2 * 2 ^ L) := by gcongr
          _ ≤ x := hx1
      rw [tent_right x hxr]
      set k' := 2 ^ (L + 1) - 1 - k with hk'
      have hk'lt : k' < 2 ^ L := by
        have : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
        omega
      have hk'cast : (k' : ℝ) = 2 * 2 ^ L - 1 - k := by
        have h2 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
        have hle : k + 1 ≤ 2 ^ (L + 1) := by omega
        rw [hk']
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
      have hx1' : (k : ℝ) ≤ x * (2 * 2 ^ L) := (div_le_iff₀ (by positivity)).mp hx1
      have hx2' : x * (2 * 2 ^ L) ≤ (k : ℝ) + 1 := (le_div_iff₀ (by positivity)).mp hx2
      rw [ih k' hk'lt (2 - 2 * x)
        (by rw [div_le_iff₀ hP, hk'cast]; nlinarith [hx1', hx2'])
        (by rw [le_div_iff₀ hP, hk'cast]; nlinarith [hx1', hx2'])]
      have hpar : Even k' ↔ ¬ Even k := by
        have h2 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
        have hsum : k' + k + 1 = 2 * 2 ^ L := by omega
        constructor
        · intro he hk2
          have : Even (k' + k + 1) := by rw [hsum]; exact even_two_mul _
          rw [Nat.even_add_one] at this
          exact this (he.add hk2)
        · intro hne
          have : Even (k' + k + 1) := by rw [hsum]; exact even_two_mul _
          rw [Nat.even_add_one, Nat.even_add] at this
          tauto
      unfold piece
      by_cases he : Even k
      · rw [ite_eq_right (hpar.not.mpr (not_not.mpr he)), ite_eq_left he, hk'cast]; ring
      · rw [ite_eq_left (hpar.mpr he), ite_eq_right he, hk'cast]; ring

/-- (4) 格子の点での値：k が偶数なら 0、奇数なら 1（0 ≤ k < 2^L）。 -/
theorem tent_iterate_grid (L k : ℕ) (hk : k < 2 ^ L) :
    tent^[L] ((k : ℝ) / 2 ^ L) = if Even k then 0 else 1 := by
  have hP : (0 : ℝ) < 2 ^ L := by positivity
  rw [tent_iterate L k hk _ le_rfl (by gcongr; linarith)]
  unfold piece
  split_ifs <;> field_simp <;> ring

/-! ### (5)(6) 折れ目と、一層で要る ReLU の数 -/

/-- (5) 内側の格子の点 k/2^L（0 < k < 2^L）では、t の L 回合成は微分できない。 -/
theorem not_differentiable_at_grid (L k : ℕ) (hk0 : 0 < k) (hk : k < 2 ^ L) :
    ¬ DifferentiableAt ℝ (tent^[L]) ((k : ℝ) / 2 ^ L) := by
  intro hd
  set p : ℝ := (k : ℝ) / 2 ^ L
  have hP : (0 : ℝ) < 2 ^ L := by positivity
  set D := deriv (tent^[L]) p
  have hD : HasDerivAt (tent^[L]) D p := hd.hasDerivAt
  -- 左の区間 k − 1 と右の区間 k の上の一次式
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hl : ∀ x ∈ Icc ((j : ℝ) / 2 ^ L) p, tent^[L] x = piece L j x := by
    intro x hx
    apply tent_iterate L j (by omega) x hx.1
    have : p = ((j : ℝ) + 1) / 2 ^ L := by simp [p]
    rw [← this]; exact hx.2
  have hr : ∀ x ∈ Icc p (((j : ℝ) + 2) / 2 ^ L), tent^[L] x = piece L (j + 1) x := by
    intro x hx
    apply tent_iterate L (j + 1) hk x hx.1
    have : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    rw [this]; exact hx.2
  have hlt1 : (j : ℝ) / 2 ^ L < p := by
    simp only [p]; push_cast; gcongr; linarith
  have hlt2 : p < ((j : ℝ) + 2) / 2 ^ L := by
    simp only [p]; push_cast; gcongr; linarith
  -- 一次式の傾き
  have slope : ∀ m : ℕ, HasDerivAt (piece L m) (if Even m then 2 ^ L else -2 ^ L) p := by
    intro m
    unfold piece
    split_ifs
    · simpa using ((hasDerivAt_id' p).const_mul ((2 : ℝ) ^ L)).sub_const (m : ℝ)
    · simpa using ((hasDerivAt_id' p).const_mul ((2 : ℝ) ^ L)).const_sub ((m : ℝ) + 1)
  have hDl : D = if Even j then 2 ^ L else -2 ^ L := by
    have h1 : HasDerivWithinAt (piece L j) D (Icc ((j : ℝ) / 2 ^ L) p) p :=
      (hD.hasDerivWithinAt).congr (fun x hx => (hl x hx).symm) (hl p ⟨hlt1.le, le_rfl⟩).symm
    exact (uniqueDiffOn_Icc hlt1 p ⟨hlt1.le, le_rfl⟩).eq_deriv _ h1 (slope j).hasDerivWithinAt
  have hDr : D = if Even (j + 1) then 2 ^ L else -2 ^ L := by
    have h1 : HasDerivWithinAt (piece L (j + 1)) D (Icc p (((j : ℝ) + 2) / 2 ^ L)) p :=
      (hD.hasDerivWithinAt).congr (fun x hx => (hr x hx).symm) (hr p ⟨le_rfl, hlt2.le⟩).symm
    exact (uniqueDiffOn_Icc hlt2 p ⟨le_rfl, hlt2.le⟩).eq_deriv _ h1 (slope (j + 1)).hasDerivWithinAt
  rw [hDl] at hDr
  by_cases he : Even j
  · have : ¬ Even (j + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
    rw [ite_eq_left he, ite_eq_right this] at hDr
    linarith
  · have : Even (j + 1) := by rw [Nat.even_add_one]; exact he
    rw [ite_eq_right he, ite_eq_left this] at hDr
    linarith

/-- 一層の ReLU の網：c₀ + c₁x + Σᵢ aᵢ ReLU(wᵢx − bᵢ)。 -/
noncomputable def shallow {N : ℕ} (c0 c1 : ℝ) (a w b : Fin N → ℝ) (x : ℝ) : ℝ :=
  c0 + c1 * x + ∑ i, a i * relu (w i * x - b i)

/-- ReLU(wx − b) は、折れ目（w ≠ 0 で wx = b）でない点で微分できる。 -/
theorem relu_affine_differentiableAt (w b x : ℝ) (h : w = 0 ∨ w * x - b ≠ 0) :
    DifferentiableAt ℝ (fun x => relu (w * x - b)) x := by
  rcases h with h | h
  · subst h
    simp only [zero_mul, zero_sub]
    exact differentiableAt_const _
  · rcases lt_or_gt_of_ne h with hneg | hpos
    · have : (fun x => relu (w * x - b)) =ᶠ[nhds x] fun _ => 0 := by
        have hc : Continuous fun x : ℝ => w * x - b := by fun_prop
        filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hneg)] with y hy
        simp [relu, max_eq_left hy.le]
      exact this.differentiableAt_iff.mpr (differentiableAt_const _)
    · have : (fun x => relu (w * x - b)) =ᶠ[nhds x] fun y => w * y - b := by
        have hc : Continuous fun x : ℝ => w * x - b := by fun_prop
        filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
        simp [relu, max_eq_right hy.le]
      exact this.differentiableAt_iff.mpr (by fun_prop)

/-- 一層の網は、どの ReLU の折れ目でもない点で微分できる。 -/
theorem shallow_differentiableAt {N : ℕ} (c0 c1 : ℝ) (a w b : Fin N → ℝ) (x : ℝ)
    (h : ∀ i, w i = 0 ∨ w i * x - b i ≠ 0) : DifferentiableAt ℝ (shallow c0 c1 a w b) x := by
  unfold shallow
  have hsum : DifferentiableAt ℝ (fun x => ∑ i, a i * relu (w i * x - b i)) x := by
    have := DifferentiableAt.fun_sum (u := Finset.univ)
      (A := fun i x => a i * relu (w i * x - b i))
      (fun i _ => (relu_affine_differentiableAt (w i) (b i) x (h i)).const_mul (a i))
    exact this
  exact ((differentiableAt_const c0).add ((differentiableAt_id).const_mul c1)).add hsum

/-- (6) 一層の ReLU の網が [0, 1] で t の L 回合成と一致するなら、ReLU の数は 2^L − 1 以上。 -/
theorem shallow_needs_many {N : ℕ} (L : ℕ) (c0 c1 : ℝ) (a w b : Fin N → ℝ)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1, shallow c0 c1 a w b x = tent^[L] x) :
    2 ^ L - 1 ≤ N := by
  have hP : (0 : ℝ) < 2 ^ L := by positivity
  -- 内側の格子の点 k = 1, …, 2^L − 1 のそれぞれに、そこを折れ目とする ReLU が一つある
  have key : ∀ m : Fin (2 ^ L - 1), ∃ i : Fin N,
      w i ≠ 0 ∧ w i * (((m : ℕ) + 1 : ℕ) / 2 ^ L : ℝ) - b i = 0 := by
    intro m
    by_contra hno
    push Not at hno
    set k := (m : ℕ) + 1
    have hk0 : 0 < k := Nat.succ_pos _
    have hk : k < 2 ^ L := by have := m.isLt; omega
    have hdiff := shallow_differentiableAt c0 c1 a w b ((k : ℝ) / 2 ^ L) (fun i => by
      by_cases hw : w i = 0
      · exact Or.inl hw
      · exact Or.inr (hno i hw))
    apply not_differentiable_at_grid L k hk0 hk
    have hp0 : 0 < (k : ℝ) / 2 ^ L := by positivity
    have hp1 : (k : ℝ) / 2 ^ L < 1 := by
      rw [div_lt_one hP]; exact_mod_cast hk
    have : shallow c0 c1 a w b =ᶠ[nhds ((k : ℝ) / 2 ^ L)] tent^[L] := by
      filter_upwards [Ioo_mem_nhds hp0 hp1] with y hy
      exact heq y ⟨hy.1.le, hy.2.le⟩
    exact this.differentiableAt_iff.mp hdiff
  choose f hf using key
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 := (hf m).2
    have h2 := (hf m').2
    rw [hmm] at h1
    have hw := (hf m').1
    have : (((m : ℕ) + 1 : ℕ) : ℝ) / 2 ^ L = (((m' : ℕ) + 1 : ℕ) : ℝ) / 2 ^ L := by
      have := mul_left_cancel₀ hw (by linarith : w (f m') * ((((m : ℕ) + 1 : ℕ) : ℝ) / 2 ^ L) =
        w (f m') * ((((m' : ℕ) + 1 : ℕ) : ℝ) / 2 ^ L))
      exact this
    rw [div_left_inj₀ hP.ne'] at this
    have : (m : ℕ) + 1 = (m' : ℕ) + 1 := by exact_mod_cast this
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective f hinj
  simpa using this

end Paper745

end Yamagishi
