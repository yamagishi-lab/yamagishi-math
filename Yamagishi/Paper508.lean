/-
論文508『弦を一本足すと、局所で確かめられる性質だけが壊れる』の格上げ（一般の形）。

原稿（508_yamagishi_only_the_local_certificate_breaks/…_jp.tex）は、六角形（n = 6）に向かい合う弦を
一本足した一例で、弦を使う閉路が頂点を尽くせないことを述べ、全走査でハミルトン閉路が 2 本
（往路と復路）のままであることを数えている。ほかの n は輪グラフ自身の数え上げだけ。

ここで証明した言明：
  (1) `edge_sets_eq_of_deg_eq`（芯・組合せ）：辺の集まり E が n + 1 本以下のとき、E の中の n 本ずつの
      二つの部分 C₁, C₂ が、どの頂点でも同じ次数（その頂点を含む辺の数）をもてば、C₁ = C₂。
  (2) `hamiltonianCycle_edges_eq`：頂点 n 個・辺 n + 1 本以下の単純グラフでは、二つのハミルトン閉路は
      （出発点や向きによらず）同じ辺の集まりを通る。輪 C_n に弦を一本足したグラフ（辺 n + 1 本）は
      その特別な場合なので、ハミルトン閉路はもとの輪ただ一つ（向きと出発点を区別しなければ）。
  (3) `K4_two_cycles`：辺を n + 2 本にすると (2) は崩れる（完全グラフ K₄：頂点 4、辺 6。辺の集まりの
      違う二つのハミルトン閉路がある）。n + 1 は最良。
形式化していないもの：オイラー回路の消え方、全走査の本数 (n − 1)!、局所の証書の話、分離子の読み。
同じ辺の集まりを通る閉路が「出発点と向きを除いて同じ」であることは、辺の集まりの等しさとして述べた。

2026-11-21 山岸勇輝（Lean での試し書き・機械による確かめ）
-/
import Mathlib

namespace Yamagishi

namespace Paper508

open Finset

variable {V : Type*} [DecidableEq V]

/-- 辺の集まり C の中で、頂点 v を含む辺の数（次数）。 -/
def deg (C : Finset (Sym2 V)) (v : V) : ℕ := (C.filter (fun e => v ∈ e)).card

theorem deg_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (v : V) :
    deg (A ∪ B) v = deg A v + deg B v := by
  unfold deg
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem deg_singleton (e : Sym2 V) (v : V) : deg {e} v = if v ∈ e then 1 else 0 := by
  unfold deg
  rw [filter_singleton]
  split_ifs <;> simp

/-- (1) 芯：辺 n + 1 本以下の中で、n 本で次数のそろう二つの部分は等しい。 -/
theorem edge_sets_eq_of_deg_eq {E C₁ C₂ : Finset (Sym2 V)} {n : ℕ}
    (h₁ : C₁ ⊆ E) (h₂ : C₂ ⊆ E) (hc₁ : C₁.card = n) (hc₂ : C₂.card = n)
    (hE : E.card ≤ n + 1) (hd : ∀ v, deg C₁ v = deg C₂ v) : C₁ = C₂ := by
  by_contra hne
  have hu : (C₁ ∪ C₂).card ≤ n + 1 := (card_le_card (union_subset h₁ h₂)).trans hE
  have hui := card_union_add_card_inter C₁ C₂
  have hs₁ := card_sdiff_add_card_inter C₁ C₂
  have hs₂ := card_sdiff_add_card_inter C₂ C₁
  rw [inter_comm] at hs₂
  -- 差の部分はどちらも 1 本
  have hd₁ : (C₁ \ C₂).card = 1 := by
    have hle : (C₁ \ C₂).card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
    · exfalso
      have hsub : C₁ ⊆ C₂ := sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 h)
      exact hne (eq_of_subset_of_card_le hsub (by omega))
    · exact h
  have hd₂ : (C₂ \ C₁).card = 1 := by omega
  obtain ⟨e, he⟩ := card_eq_one.1 hd₁
  obtain ⟨f, hf⟩ := card_eq_one.1 hd₂
  -- 次数の分け方
  have split₁ : ∀ v, deg C₁ v = deg (C₁ ∩ C₂) v + deg {e} v := by
    intro v
    rw [← he, ← deg_union_of_disjoint (disjoint_sdiff_inter C₁ C₂).symm, union_comm,
      sdiff_union_inter]
  have split₂ : ∀ v, deg C₂ v = deg (C₁ ∩ C₂) v + deg {f} v := by
    intro v
    rw [← hf, inter_comm, ← deg_union_of_disjoint (disjoint_sdiff_inter C₂ C₁).symm, union_comm,
      sdiff_union_inter]
  have hef : e = f := by
    apply Sym2.ext
    intro v
    have := hd v
    rw [split₁, split₂, deg_singleton, deg_singleton] at this
    constructor
    · intro hv; by_contra hv'; simp [hv, hv'] at this
    · intro hv; by_contra hv'; simp [hv, hv'] at this
  have heC : e ∈ C₁ \ C₂ := by rw [he]; exact mem_singleton_self e
  have hfC : f ∈ C₂ \ C₁ := by rw [hf]; exact mem_singleton_self f
  rw [hef] at heC
  exact (mem_sdiff.1 heC).2 (mem_sdiff.1 hfC).1

/-- 次数を、Mathlib の近傍の集合の大きさに読み替える。 -/
theorem deg_eq_ncard (C : Finset (Sym2 V)) (v : V) :
    deg C v = {w | s(v, w) ∈ C}.ncard := by
  unfold deg
  rw [← Set.ncard_coe_finset]
  have : (↑(C.filter (fun e => v ∈ e)) : Set (Sym2 V)) =
      (fun w => s(v, w)) '' {w | s(v, w) ∈ C} := by
    ext e
    simp only [coe_filter, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨heC, hv⟩
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
      exact ⟨w, heC, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, Sym2.mem_mk_left v w⟩
  rw [this, Set.ncard_image_of_injective _ (fun a b h => Sym2.congr_right.1 h)]

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- ハミルトン閉路の辺の集まりは、辺 n 本、どの頂点でも次数 2。 -/
theorem hamCycle_props {a : V} {p : G.Walk a a} (hp : p.IsHamiltonianCycle) :
    p.edges.toFinset ⊆ G.edgeFinset ∧ p.edges.toFinset.card = Fintype.card V ∧
      ∀ v, deg p.edges.toFinset v = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.1 he)
  · rw [List.toFinset_card_of_nodup hp.isCycle.edges_nodup, SimpleGraph.Walk.length_edges,
      hp.length_eq]
  · intro v
    rw [deg_eq_ncard, ← hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support v)]
    congr 1
    ext w
    simp [SimpleGraph.Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]

/-- (2) 頂点 n 個・辺 n + 1 本以下なら、ハミルトン閉路の辺の集まりはただ一つ。 -/
theorem hamiltonianCycle_edges_eq (hE : G.edgeFinset.card ≤ Fintype.card V + 1)
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsHamiltonianCycle) (hq : q.IsHamiltonianCycle) :
    p.edges.toFinset = q.edges.toFinset := by
  obtain ⟨hp1, hp2, hp3⟩ := hamCycle_props hp
  obtain ⟨hq1, hq2, hq3⟩ := hamCycle_props hq
  exact edge_sets_eq_of_deg_eq hp1 hq1 hp2 hq2 hE (fun v => by rw [hp3, hq3])

/-- K₄ の一つめの閉路 0 → 1 → 2 → 3 → 0。 -/
def k4p : (⊤ : SimpleGraph (Fin 4)).Walk 0 0 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 1 2) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 2 3) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 3 0) .nil

/-- K₄ の二つめの閉路 0 → 1 → 3 → 2 → 0（対角線を二本使う）。 -/
def k4q : (⊤ : SimpleGraph (Fin 4)).Walk 0 0 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 1 3) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 3 2) <|
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 2 0) .nil

/-- (3) 辺 n + 2 本では崩れる：K₄（頂点 4・辺 6）に、辺の集まりの違う二つのハミルトン閉路がある。 -/
theorem K4_two_cycles :
    (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = Fintype.card (Fin 4) + 2 ∧
      k4p.IsHamiltonianCycle ∧ k4q.IsHamiltonianCycle ∧
      k4p.edges.toFinset ≠ k4q.edges.toFinset := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one,
      SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    refine ⟨⟨by decide, by simp [k4p], by decide⟩, by decide⟩
  · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one,
      SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    refine ⟨⟨by decide, by simp [k4q], by decide⟩, by decide⟩

end Paper508

end Yamagishi
