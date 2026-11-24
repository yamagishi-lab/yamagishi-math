/-
論文622『数字を並べ替えて引く操作は、4 桁なら 6174 に着き、5 桁では着く先が無い』の格上げ（一般の形）。

日本語の一文：十進で d 桁（先頭の 0 も桁に数える）のカプレカー写像（大きい順に並べた数から小さい順に
並べた数を引く）が 0 でない不動点を持たないのは、d ≥ 2 のうち d = 2・5・7 のときだけである。
English: For every d ≥ 2, the d-digit Kaprekar map (leading zeros counted; largest arrangement minus
smallest) has a nonzero fixed point exactly when d is not 2, 5 or 7.

原稿（622_yamagishi_sorting_digits_reaches_6174_but_not_for_five/…_jp.tex）は、2〜6 桁の全部の出発点の
行き先と、組み合わせからの不動点探し（2・5 桁は無し、3・4・6 桁は在る）を示している。一般の桁は扱わない
と書いている。

ここで証明した言明（`kap d n` は n の下から d 桁を並べ替えて引いた数）：
  (1) `kap_two`・`kap_five`・`kap_seven`：大きい順の数字を a₁ ≥ … ≥ a_d とすると、
      2 桁で 9(a₁ − a₂)、5 桁で 9999(a₁ − a₅) + 990(a₂ − a₄)、7 桁で 999999(a₁ − a₇) +
      99990(a₂ − a₆) + 9900(a₃ − a₅)（写像の値は数字の差だけで決まる）。
  (2) `no_fixed_two`・`no_fixed_five`・`no_fixed_seven`：2・5・7 桁では 0 でない不動点は無い
      （(1) で候補を 10・55・220 個に絞り、その一つ一つを `decide` で確かめた）。
  (3) `fixed_three` などの具体例：495（3 桁）、6174（4 桁）、631764（6 桁）、63317664（8 桁）、
      864197532（9 桁）、6333176664（10 桁）、86431976532（11 桁）、633331766664（12 桁）は不動点。
      `fixed_iff`：2 ≤ d ≤ 12 で、0 でない不動点が在る ⇔ d ∉ {2, 5, 7}。
  (4) `famEven_fixed`：すべての j ≥ 0 で 6 3^j 1 7 6^j 4（2j + 4 桁）は不動点。
      `famOdd_fixed`：すべての j ≥ 0 で 8 6 4 3^j 1 9 7 6^j 5 3 2（2j + 9 桁）は不動点。
      芯は `fixed_of_blocks`（数字の並べ替えを並びの一致で決め、ofList の等式に帰着）と、
      9·(c が j 個並んだ数) + c = c·10^j。
  (5) `fixed_iff_all`：すべての d ≥ 2 で、0 でない不動点が在る ⇔ d ∉ {2, 5, 7}。
足した仮定：なし（有限の確かめは、Lean の核が確かめる `decide` だけ）。下読みの AI の案の三つの
族のうち、5^(k−1) 4 9^k 4^(k−1) 5（3k 桁）は要らなかった（偶数の桁は一つ目の族、9 桁以上の奇数の桁は
三つ目の族、3 桁は 495 で足りる）。
形式化していないもの：全部の出発点が一つの不動点に着くこと（3・4 桁のカプレカー定数）、原稿の手数の
分布と輪の数（48480・48320・3190 など）、分離子の読み。

2026-11-24 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper622

/-- 下の桁から d 桁（先頭の 0 も数える）。 -/
def digs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | d + 1, n => n % 10 :: digs d (n / 10)

/-- 上の桁から読んだ数。 -/
def ofList (l : List ℕ) : ℕ := l.foldl (fun acc x => 10 * acc + x) 0

/-- 大きい順に並べた数字。 -/
def desc (d n : ℕ) : List ℕ := (digs d n).insertionSort (· ≥ ·)

/-- カプレカー写像：大きい順の数 − 小さい順の数。 -/
def kap (d n : ℕ) : ℕ := ofList (desc d n) - ofList (desc d n).reverse

/-- 0 でない不動点が在る。 -/
def HasFixed (d : ℕ) : Prop := ∃ n, n < 10 ^ d ∧ n ≠ 0 ∧ kap d n = n

theorem digs_length (d n : ℕ) : (digs d n).length = d := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih => simp [digs, ih]

theorem digs_lt (d n : ℕ) : ∀ x ∈ digs d n, x < 10 := by
  induction d generalizing n with
  | zero => simp [digs]
  | succ d ih =>
    intro x hx
    simp only [digs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by norm_num)
    · exact ih _ x hx

theorem desc_length (d n : ℕ) : (desc d n).length = d := by
  unfold desc; rw [(List.perm_insertionSort _ _).length_eq, digs_length]

theorem desc_lt (d n : ℕ) : ∀ x ∈ desc d n, x < 10 := by
  intro x hx
  unfold desc at hx
  exact digs_lt d n x ((List.perm_insertionSort _ _).mem_iff.mp hx)

theorem desc_sorted (d n : ℕ) : (desc d n).Pairwise (· ≥ ·) := by
  unfold desc; exact List.pairwise_insertionSort _ _

/-- (1) 2 桁：kap = 9(a₁ − a₂)。 -/
theorem kap_two (n : ℕ) : ∃ x, x ≤ 9 ∧ kap 2 n = 9 * x := by
  have hl := desc_length 2 n
  have hs := desc_sorted 2 n
  have hb := desc_lt 2 n
  unfold kap
  generalize desc 2 n = L at hl hs hb
  match L, hl with
  | [a, b], _ =>
    simp [List.pairwise_cons] at hs
    have ha := hb a (by simp)
    refine ⟨a - b, by omega, ?_⟩
    simp [ofList]
    omega

/-- (1) 5 桁：kap = 9999(a₁ − a₅) + 990(a₂ − a₄)。 -/
theorem kap_five (n : ℕ) :
    ∃ x y, y ≤ x ∧ x ≤ 9 ∧ kap 5 n = 9999 * x + 990 * y := by
  have hl := desc_length 5 n
  have hs := desc_sorted 5 n
  have hb := desc_lt 5 n
  unfold kap
  generalize desc 5 n = L at hl hs hb
  match L, hl with
  | [a, b, c, e, f], _ =>
    simp [List.pairwise_cons] at hs
    have ha := hb a (by simp)
    refine ⟨a - f, b - e, by omega, by omega, ?_⟩
    simp [ofList]
    omega

/-- (1) 7 桁：kap = 999999(a₁ − a₇) + 99990(a₂ − a₆) + 9900(a₃ − a₅)。 -/
theorem kap_seven (n : ℕ) :
    ∃ x y z, z ≤ y ∧ y ≤ x ∧ x ≤ 9 ∧ kap 7 n = 999999 * x + 99990 * y + 9900 * z := by
  have hl := desc_length 7 n
  have hs := desc_sorted 7 n
  have hb := desc_lt 7 n
  unfold kap
  generalize desc 7 n = L at hl hs hb
  match L, hl with
  | [a, b, c, e, f, g, h], _ =>
    simp [List.pairwise_cons] at hs
    have ha := hb a (by simp)
    refine ⟨a - h, b - g, c - f, by omega, by omega, by omega, ?_⟩
    simp [ofList]
    omega

/-- 有限の確かめ：2 桁の候補 9x。 -/
theorem check_two : ∀ x < 10, 9 * x ≠ 0 → kap 2 (9 * x) ≠ 9 * x := by decide

/-- 有限の確かめ：5 桁の候補 9999x + 990y（y ≤ x ≤ 9）。 -/
theorem check_five : ∀ x < 10, ∀ y < x + 1,
    9999 * x + 990 * y ≠ 0 → kap 5 (9999 * x + 990 * y) ≠ 9999 * x + 990 * y := by decide

/-- 有限の確かめ：7 桁の候補（z ≤ y ≤ x ≤ 9）。 -/
theorem check_seven : ∀ x < 10, ∀ y < x + 1, ∀ z < y + 1,
    999999 * x + 99990 * y + 9900 * z ≠ 0 →
      kap 7 (999999 * x + 99990 * y + 9900 * z) ≠ 999999 * x + 99990 * y + 9900 * z := by
  decide

/-- (2) 2 桁では 0 でない不動点は無い。 -/
theorem no_fixed_two : ¬ HasFixed 2 := by
  rintro ⟨n, _, hn0, hfix⟩
  obtain ⟨x, hx, hk⟩ := kap_two n
  have hN : n = 9 * x := by rw [← hfix, hk]
  have h1 : 9 * x ≠ 0 := by rw [← hN]; exact hn0
  have := check_two x (by omega) h1
  rw [← hN] at this
  exact this hfix

/-- (2) 5 桁では 0 でない不動点は無い。 -/
theorem no_fixed_five : ¬ HasFixed 5 := by
  rintro ⟨n, _, hn0, hfix⟩
  obtain ⟨x, y, hyx, hx, hk⟩ := kap_five n
  have hN : n = 9999 * x + 990 * y := by rw [← hfix, hk]
  have h1 : 9999 * x + 990 * y ≠ 0 := by rw [← hN]; exact hn0
  have := check_five x (by omega) y (by omega) h1
  rw [← hN] at this
  exact this hfix

/-- (2) 7 桁では 0 でない不動点は無い。 -/
theorem no_fixed_seven : ¬ HasFixed 7 := by
  rintro ⟨n, _, hn0, hfix⟩
  obtain ⟨x, y, z, hzy, hyx, hx, hk⟩ := kap_seven n
  have hN : n = 999999 * x + 99990 * y + 9900 * z := by rw [← hfix, hk]
  have h1 : 999999 * x + 99990 * y + 9900 * z ≠ 0 := by rw [← hN]; exact hn0
  have := check_seven x (by omega) y (by omega) z (by omega) h1
  rw [← hN] at this
  exact this hfix

/-! ### (3) 不動点の具体例 -/

theorem fixed_three : HasFixed 3 := ⟨495, by norm_num, by norm_num, by decide⟩
theorem fixed_four : HasFixed 4 := ⟨6174, by norm_num, by norm_num, by decide⟩
theorem fixed_six : HasFixed 6 := ⟨631764, by norm_num, by norm_num, by decide⟩
theorem fixed_eight : HasFixed 8 := ⟨63317664, by norm_num, by norm_num, by decide⟩
theorem fixed_nine : HasFixed 9 := ⟨864197532, by norm_num, by norm_num, by decide⟩
theorem fixed_ten : HasFixed 10 := ⟨6333176664, by norm_num, by norm_num, by decide⟩
theorem fixed_eleven : HasFixed 11 := ⟨86431976532, by norm_num, by norm_num, by decide⟩
theorem fixed_twelve : HasFixed 12 := ⟨633331766664, by norm_num, by norm_num, by decide⟩

/-- (4) 2 ≤ d ≤ 12 で、0 でない不動点が在る ⇔ d ∉ {2, 5, 7}。 -/
theorem fixed_iff {d : ℕ} (h2 : 2 ≤ d) (h12 : d ≤ 12) :
    HasFixed d ↔ d ≠ 2 ∧ d ≠ 5 ∧ d ≠ 7 := by
  interval_cases d
  · exact ⟨fun h => absurd h no_fixed_two, fun h => absurd rfl h.1⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_three⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_four⟩
  · exact ⟨fun h => absurd h no_fixed_five, fun h => absurd rfl h.2.1⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_six⟩
  · exact ⟨fun h => absurd h no_fixed_seven, fun h => absurd rfl h.2.2⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_eight⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_nine⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_ten⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_eleven⟩
  · exact ⟨fun _ => by decide, fun _ => fixed_twelve⟩

/-! ### 一般の桁：二つの族 -/

theorem foldl_shift (L : List ℕ) (a : ℕ) :
    L.foldl (fun acc x => 10 * acc + x) a = a * 10 ^ L.length + ofList L := by
  induction L generalizing a with
  | nil => simp [ofList]
  | cons x L ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, show ofList (x :: L) = L.foldl (fun acc x => 10 * acc + x) (10 * 0 + x) from rfl, ih]
    ring

theorem ofList_append (L1 L2 : List ℕ) :
    ofList (L1 ++ L2) = ofList L1 * 10 ^ L2.length + ofList L2 := by
  unfold ofList
  rw [List.foldl_append, foldl_shift]
  rfl

theorem ofList_replicate (k c : ℕ) : 9 * ofList (List.replicate k c) + c = c * 10 ^ k := by
  induction k with
  | zero => simp [ofList]
  | succ k ih =>
    rw [List.replicate_succ', ofList_append]
    simp only [List.length_singleton, pow_succ]
    have : ofList [c] = c := by simp [ofList]
    rw [this]
    nlinarith [ih]

theorem digs_ofList (L : List ℕ) (h : ∀ x ∈ L, x < 10) : digs L.length (ofList L) = L.reverse := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L x ih =>
    have hx : x < 10 := h x (by simp)
    have hL : ∀ y ∈ L, y < 10 := fun y hy => h y (by simp [hy])
    rw [List.length_append, List.length_singleton, ofList_append, List.length_singleton, pow_one]
    have : ofList [x] = x := by simp [ofList]
    rw [this]
    simp only [digs, List.reverse_append, List.reverse_singleton, List.singleton_append]
    have h1 : (ofList L * 10 + x) % 10 = x := by omega
    have h2 : (ofList L * 10 + x) / 10 = ofList L := by omega
    rw [h1, h2, ih hL]

/-- 族の芯：数字の並び F の並べ替えが T（大きい順）で、ofList T = ofList F + ofList T.reverse なら、
F の数は不動点。 -/
theorem fixed_of_blocks (F T : List ℕ) (hF : ∀ x ∈ F, x < 10) (hT : T.Pairwise (· ≥ ·))
    (hp : F.Perm T) (heq : ofList T = ofList F + ofList T.reverse) :
    kap F.length (ofList F) = ofList F := by
  have hd : desc F.length (ofList F) = T := by
    unfold desc
    rw [digs_ofList F hF]
    apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
      (fun a b _ _ h1 h2 => le_antisymm h2 h1) (List.pairwise_insertionSort _ _) hT
    exact (List.perm_insertionSort _ _).trans ((List.reverse_perm F).trans hp)
  unfold kap
  rw [hd]
  omega

/-- 偶数の桁の族 6 3^j 1 7 6^j 4（2j + 4 桁）。 -/
def famEven (j : ℕ) : List ℕ := [6] ++ List.replicate j 3 ++ [1, 7] ++ List.replicate j 6 ++ [4]

theorem famEven_fixed (j : ℕ) :
    kap (2 * j + 4) (ofList (famEven j)) = ofList (famEven j) := by
  set T := [7, 6] ++ List.replicate j 6 ++ [4] ++ List.replicate j 3 ++ [1] with hTdef
  have hlen : (famEven j).length = 2 * j + 4 := by simp [famEven]; ring
  rw [← hlen]
  apply fixed_of_blocks (famEven j) T
  · intro x hx
    simp [famEven] at hx
    omega
  · simp [hTdef, List.pairwise_append, List.pairwise_cons, List.pairwise_replicate]
    refine ⟨fun a ha => by omega, fun a ha => by omega, fun a ha => by omega,
      fun _ a ha => by omega⟩
  · rw [List.perm_iff_count]
    intro a
    simp only [famEven, hTdef, List.count_append, List.count_cons, List.count_nil,
      List.count_replicate]
    split_ifs <;> omega
  · have h3 := ofList_replicate j 3
    have h6 := ofList_replicate j 6
    simp only [hTdef, famEven, List.reverse_append, List.reverse_replicate, List.reverse_cons,
      List.reverse_nil, ofList_append, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    have e1 : ofList [7, 6] = 76 := by simp [ofList]
    have e2 : ofList [4] = 4 := by simp [ofList]
    have e3 : ofList [1] = 1 := by simp [ofList]
    have e4 : ofList [6] = 6 := by simp [ofList]
    have e5 : ofList [1, 7] = 17 := by simp [ofList]
    have e6 : ofList ([] : List ℕ) = 0 := rfl
    have e7 : ofList [7] = 7 := by simp [ofList]
    simp only [e1, e2, e3, e4, e5, e6, e7]
    simp only [pow_add, pow_succ, pow_zero, zero_add, one_mul, zero_mul]
    generalize 10 ^ j = P at *
    generalize ofList (List.replicate j 3) = R3 at *
    generalize ofList (List.replicate j 6) = R6 at *
    qify at h3 h6 ⊢
    linear_combination (-10 * (200 * P - 1) / 9 : ℚ) * h3 + (10 * (10 * P - 11) / 9 : ℚ) * h6

/-- 奇数の桁の族 8 6 4 3^j 1 9 7 6^j 5 3 2（2j + 9 桁）。 -/
def famOdd (j : ℕ) : List ℕ :=
  [8, 6, 4] ++ List.replicate j 3 ++ [1, 9, 7] ++ List.replicate j 6 ++ [5, 3, 2]

theorem famOdd_fixed (j : ℕ) :
    kap (2 * j + 9) (ofList (famOdd j)) = ofList (famOdd j) := by
  set T := [9, 8, 7, 6] ++ List.replicate j 6 ++ [5, 4, 3] ++ List.replicate j 3 ++ [2, 1]
    with hTdef
  have hlen : (famOdd j).length = 2 * j + 9 := by simp [famOdd]; ring
  rw [← hlen]
  apply fixed_of_blocks (famOdd j) T
  · intro x hx
    simp [famOdd] at hx
    omega
  · simp [hTdef, List.pairwise_append, List.pairwise_cons, List.pairwise_replicate]
    repeat' apply And.intro
    all_goals intros; omega
  · rw [List.perm_iff_count]
    intro a
    simp only [famOdd, hTdef, List.count_append, List.count_cons, List.count_nil,
      List.count_replicate]
    split_ifs <;> omega
  · have h3 := ofList_replicate j 3
    have h6 := ofList_replicate j 6
    simp only [hTdef, famOdd, List.reverse_append, List.reverse_replicate, List.reverse_cons,
      List.reverse_nil, ofList_append, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    generalize ofList (List.replicate j 3) = R3 at *
    generalize ofList (List.replicate j 6) = R6 at *
    simp only [ofList, List.foldl_cons, List.foldl_nil]
    simp only [pow_add, pow_succ, pow_zero, zero_add, one_mul, zero_mul, mul_zero]
    generalize 10 ^ j = P at *
    qify at h3 h6 ⊢
    linear_combination (-100 * (110000 * P - 1) / 9 : ℚ) * h3 +
      (1000 * (100 * P - 11) / 9 : ℚ) * h6

theorem ofList_cons (a : ℕ) (L : List ℕ) : ofList (a :: L) = a * 10 ^ L.length + ofList L := by
  rw [show a :: L = [a] ++ L from rfl, ofList_append]
  simp [ofList]

theorem ofList_lt (L : List ℕ) (h : ∀ x ∈ L, x < 10) : ofList L < 10 ^ L.length := by
  induction L using List.reverseRecOn with
  | nil => simp [ofList]
  | append_singleton L x ih =>
    have hx : x < 10 := h x (by simp)
    have hL : ∀ y ∈ L, y < 10 := fun y hy => h y (by simp [hy])
    have e : ofList [x] = x := by simp [ofList]
    rw [ofList_append, List.length_singleton, pow_one, e, List.length_append,
      List.length_singleton, pow_succ]
    have := ih hL
    omega

/-- 族の数は d 桁で、0 でない不動点。 -/
theorem hasFixed_of_fam (L : List ℕ) (a : ℕ) (L' : List ℕ) (hL : L = a :: L') (ha : 0 < a)
    (hlt : ∀ x ∈ L, x < 10) (hfix : kap L.length (ofList L) = ofList L) : HasFixed L.length := by
  refine ⟨ofList L, ofList_lt L hlt, ?_, hfix⟩
  rw [hL, ofList_cons]
  have : 0 < a * 10 ^ L'.length := by positivity
  omega

theorem hasFixed_even (j : ℕ) : HasFixed (2 * j + 4) := by
  have hlen : (famEven j).length = 2 * j + 4 := by simp [famEven]; ring
  rw [← hlen]
  apply hasFixed_of_fam (famEven j) 6 (List.replicate j 3 ++ [1, 7] ++ List.replicate j 6 ++ [4])
  · simp [famEven]
  · norm_num
  · intro x hx; simp [famEven] at hx; omega
  · rw [hlen]; exact famEven_fixed j

theorem hasFixed_odd (j : ℕ) : HasFixed (2 * j + 9) := by
  have hlen : (famOdd j).length = 2 * j + 9 := by simp [famOdd]; ring
  rw [← hlen]
  apply hasFixed_of_fam (famOdd j) 8
    ([6, 4] ++ List.replicate j 3 ++ [1, 9, 7] ++ List.replicate j 6 ++ [5, 3, 2])
  · simp [famOdd]
  · norm_num
  · intro x hx; simp [famOdd] at hx; omega
  · rw [hlen]; exact famOdd_fixed j

/-- (5) すべての d ≥ 2 で、0 でない不動点が在る ⇔ d ∉ {2, 5, 7}。 -/
theorem fixed_iff_all {d : ℕ} (h2 : 2 ≤ d) : HasFixed d ↔ d ≠ 2 ∧ d ≠ 5 ∧ d ≠ 7 := by
  constructor
  · rintro h
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
    · exact no_fixed_two h
    · exact no_fixed_five h
    · exact no_fixed_seven h
  · rintro ⟨n2, n5, n7⟩
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : d = 2 * (k - 2) + 4 := by omega
      rw [this]; exact hasFixed_even _
    · by_cases h3 : d = 3
      · rw [h3]; exact fixed_three
      · have : d = 2 * (k - 4) + 9 := by omega
        rw [this]; exact hasFixed_odd _

end Paper622

end Yamagishi
