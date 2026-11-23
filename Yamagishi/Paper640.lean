/-
論文640『偶数を二つの素数の和に表す仕方の数は、3 で割り切れるかでおよそ 2 倍違う』の芯
（余りの数え上げ。漸近の部分は止めた）。

日本語：奇素数 ℓ について、0 でない余りの組 (r, s) で r + s ≡ c となるものは、c ≡ 0 なら ℓ − 1 組、
そうでなければ ℓ − 2 組ある。素数の組が余りの組に一様に分かれるなら、ℓ で割り切れる偶数の平均と
割り切れない偶数の平均の比は (ℓ − 1)/(ℓ − 2) になり、いくつかの素数では中国剰余定理で積になる。
English: For an odd prime ℓ there are ℓ − 1 pairs of nonzero residues with sum 0 and ℓ − 2 with any
other sum; under equidistribution of prime pairs this gives the ratio (ℓ − 1)/(ℓ − 2), and the
counts multiply over several primes by the Chinese remainder theorem.

原稿（640_yamagishi_ways_to_write_an_even_number_as_two_primes_double_when_divisible_by_3/…_jp.tex）は、
90 万〜100 万の偶数で 3・5・7 の平均の比 1.999939・1.333126・1.199996 を数え、ハーディ＝リトルウッドの
予想の式と比べ、観察 3.2 で余りの数え上げの説明を付ける。

ここで証明した言明：
  (1) `pairCount_eq`：素数 ℓ と c ∈ ℤ/ℓ について、0 でない r, s で r + s = c となる組の数は、
      c = 0 なら ℓ − 1、c ≠ 0 なら ℓ − 2。`pairCount_sum_ne_zero`：0 でない類の分を合わせると
      (ℓ − 1)(ℓ − 2)（全部で (ℓ − 1)²）。
  (2) `mean_ratio`：ℓ ≥ 3 で、和が 0 の類の組の数と、0 でない類の組の数の平均の比は (ℓ − 1)/(ℓ − 2)。
      （素数の組の余りが (ℓ − 1)² 通りに一様に分かれ、偶数が ℓ の余りに一様に分かれるときの、
      平均の比の値。）`ratio_three`・`ratio_five`・`ratio_seven`：2、4/3、6/5。
  (3) `unitPairCount_prod`：有限の可換環の積 R × S では、単元の組で和が (c, d) になる数は
      R の数 × S の数。`crt_count`：互いに素な m, n で、ℤ/(mn) の数は中国剰余定理の二つの成分の
      数の積。`two_primes`：異なる素数 ℓ₁, ℓ₂ で、和の類の数は (ℓ₁ − 1 か ℓ₁ − 2)(ℓ₂ − 1 か ℓ₂ − 2)。
      （ここから、割り切れ方の型ごとの平均の比がそれぞれの (ℓ − 1)/(ℓ − 2) の積になることは (2) と
      同じ割り算で出るが、その割り算は二つの素数については書いていない。）
止めた所：平均の比が N → ∞ で (ℓ − 1)/(ℓ − 2) に収束すること。Mathlib には算術級数の素数定理
（`Nat.isEquivalent_card_prime_modEq`）が在るが、そこから「p + q ≤ N の素数の組が余りの組に一様に
分かれる」ことを導く二次元の数え上げ（部分和の入れ替えと誤差の評価）は、ここでは形式化していない。
一つ一つの n についての倍率（ハーディ＝リトルウッドの予想）は未解決のまま。

2026-11-23 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper640

open Finset

/-! ### (1) 一つの素数での数え上げ -/

/-- 0 でない余り r, s で r + s = c となる組の数。 -/
def pairCount (ℓ : ℕ) [NeZero ℓ] (c : ZMod ℓ) : ℕ :=
  #((univ : Finset (ZMod ℓ × ZMod ℓ)).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 = c))

/-- (1) 和が c の組は、c = 0 なら ℓ − 1 組、c ≠ 0 なら ℓ − 2 組。 -/
theorem pairCount_eq (ℓ : ℕ) [Fact ℓ.Prime] (c : ZMod ℓ) :
    pairCount ℓ c = if c = 0 then ℓ - 1 else ℓ - 2 := by
  have hset : (univ : Finset (ZMod ℓ × ZMod ℓ)).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 = c)
      = ((univ : Finset (ZMod ℓ)) \ {0, c}).image (fun r => (r, c - r)) := by
    ext ⟨r, s⟩
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_sdiff, mem_insert,
      mem_singleton, not_or, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨r, ⟨h1, ?_⟩, rfl, ?_⟩
      · intro h; apply h2; rw [h] at h3; linear_combination h3
      · linear_combination -h3
    · rintro ⟨r', ⟨h1, h2⟩, rfl, rfl⟩
      refine ⟨h1, ?_, by ring⟩
      intro h; apply h2; linear_combination -h
  unfold pairCount
  rw [hset, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
    card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
  split_ifs with hc
  · rw [hc]; simp
  · rw [card_pair (Ne.symm hc)]

theorem prime_ge_two (ℓ : ℕ) [Fact ℓ.Prime] : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le

/-- (1) 0 でない類の分を合わせると (ℓ − 1)(ℓ − 2)。 -/
theorem pairCount_sum_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] :
    ∑ c ∈ (univ : Finset (ZMod ℓ)).filter (· ≠ 0), (pairCount ℓ c : ℝ) =
      ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 2) := by
  have h2 := prime_ge_two ℓ
  have e : ∀ c ∈ (univ : Finset (ZMod ℓ)).filter (· ≠ 0), (pairCount ℓ c : ℝ) = (ℓ : ℝ) - 2 := by
    intro c hc
    rw [mem_filter] at hc
    rw [pairCount_eq]
    split_ifs with h0
    · exact absurd h0 hc.2
    · push_cast [Nat.cast_sub h2]
      ring
  rw [sum_congr rfl e, sum_const, nsmul_eq_mul]
  have hcard : #((univ : Finset (ZMod ℓ)).filter (· ≠ 0)) = ℓ - 1 := by
    rw [filter_ne' univ (0 : ZMod ℓ), card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [hcard]
  push_cast [Nat.cast_sub (by omega : 1 ≤ ℓ)]
  ring

/-! ### (2) 平均の比 -/

/-- (2) ℓ ≥ 3：和が 0 の類の数 ÷（0 でない類の数の平均）= (ℓ − 1)/(ℓ − 2)。 -/
theorem mean_ratio (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 3 ≤ ℓ) :
    (pairCount ℓ 0 : ℝ) /
        ((∑ c ∈ (univ : Finset (ZMod ℓ)).filter (· ≠ 0), (pairCount ℓ c : ℝ)) / ((ℓ : ℝ) - 1)) =
      ((ℓ : ℝ) - 1) / ((ℓ : ℝ) - 2) := by
  have hp : pairCount ℓ 0 = ℓ - 1 := by
    rw [pairCount_eq]; split_ifs with h0
    · rfl
    · exact absurd rfl h0
  rw [pairCount_sum_ne_zero, hp]
  have h3 : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  push_cast [Nat.cast_sub (by omega : 1 ≤ ℓ)]
  have h1 : (ℓ : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (ℓ : ℝ) - 2 ≠ 0 := by linarith
  field_simp

theorem ratio_three : ((3 : ℝ) - 1) / (3 - 2) = 2 := by norm_num
theorem ratio_five : ((5 : ℝ) - 1) / (5 - 2) = 4 / 3 := by norm_num
theorem ratio_seven : ((7 : ℝ) - 1) / (7 - 2) = 6 / 5 := by norm_num

/-! ### (3) いくつかの素数：中国剰余定理で積になる -/

section units

open Classical

/-- 有限の可換環で、単元 r, s で r + s = c となる組の数。 -/
noncomputable def unitPairCount (R : Type*) [CommRing R] [Fintype R] (c : R) : ℕ :=
  #((univ : Finset (R × R)).filter (fun p => IsUnit p.1 ∧ IsUnit p.2 ∧ p.1 + p.2 = c))

/-- (3) 積の環では数が掛け算になる。 -/
theorem unitPairCount_prod (R S : Type*) [CommRing R] [Fintype R] [CommRing S] [Fintype S]
    (c : R) (d : S) : unitPairCount (R × S) (c, d) = unitPairCount R c * unitPairCount S d := by
  unfold unitPairCount
  rw [← card_product]
  let e : (R × S) × (R × S) ≃ (R × R) × (S × S) :=
    { toFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
      invFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  apply card_equiv e
  intro p
  simp only [mem_filter, mem_univ, true_and, mem_product, Prod.isUnit_iff, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add, e, Equiv.coe_fn_mk]
  tauto

/-- (3) 環の同型で数は変わらない。 -/
theorem unitPairCount_equiv {R S : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S]
    (f : R ≃+* S) (c : R) : unitPairCount R c = unitPairCount S (f c) := by
  unfold unitPairCount
  apply card_equiv (f.toEquiv.prodCongr f.toEquiv)
  intro p
  simp only [mem_filter, mem_univ, true_and, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, isUnit_map_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← map_add, h3]⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, f.injective (by rw [map_add, h3])⟩

/-- 素数 ℓ では、単元の組の数は 0 でない組の数と同じ。 -/
theorem unitPairCount_prime (ℓ : ℕ) [Fact ℓ.Prime] (c : ZMod ℓ) :
    unitPairCount (ZMod ℓ) c = pairCount ℓ c := by
  unfold unitPairCount pairCount
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, isUnit_iff_ne_zero]

/-- (3) 中国剰余定理：互いに素な m, n で、ℤ/(mn) の数は二つの成分の数の積。 -/
theorem crt_count {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) (c : ZMod (m * n)) :
    unitPairCount (ZMod (m * n)) c =
      unitPairCount (ZMod m) (ZMod.chineseRemainder h c).1 *
        unitPairCount (ZMod n) (ZMod.chineseRemainder h c).2 := by
  rw [unitPairCount_equiv (ZMod.chineseRemainder h) c, ← unitPairCount_prod]

/-- (3) 異なる素数 ℓ₁, ℓ₂：数は (ℓ₁ − 1 か ℓ₁ − 2) × (ℓ₂ − 1 か ℓ₂ − 2)。 -/
theorem two_primes {ℓ₁ ℓ₂ : ℕ} [Fact ℓ₁.Prime] [Fact ℓ₂.Prime] (hne : ℓ₁ ≠ ℓ₂)
    (c : ZMod (ℓ₁ * ℓ₂)) :
    unitPairCount (ZMod (ℓ₁ * ℓ₂)) c =
      (if (ZMod.chineseRemainder ((Nat.coprime_primes Fact.out Fact.out).mpr hne) c).1 = 0
        then ℓ₁ - 1 else ℓ₁ - 2) *
      (if (ZMod.chineseRemainder ((Nat.coprime_primes Fact.out Fact.out).mpr hne) c).2 = 0
        then ℓ₂ - 1 else ℓ₂ - 2) := by
  rw [crt_count, unitPairCount_prime, unitPairCount_prime, pairCount_eq, pairCount_eq]

end units

end Paper640

end Yamagishi
