/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original statement formalization: The Formal Conjectures Authors, 2026.
New independent Lean development and write-up: Wentao Li, 2026.
Mathematics: Ermelinda DeLaVina, Siemion Fajtlowicz and Bill Waller,
On Some Conjectures of Griggs and Graffiti, March 2002, revised May 2003,
Conjecture 2 and Lemma 1. This is not a new mathematical discovery.
AI assistance: Cursor Grok 4.6 Extra High.
Public Lean inspected and not copied: kingcharlezz WOWII GraphConjecture2
pendant-attachment (different theorem); AlphaProof Nexus GraphConjecture2
(different average-neighborhood bound).
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic

/-!
Independent Lean proof of
`WrittenOnTheWallII.GraphConjecture7.conjecture7`.

This file does not import the frozen sorry theorem. It uses the existing
`Ls` / `indepNeighborsCard` / `indepNum` API unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

open scoped Classical
open SimpleGraph Finset

namespace WOWII7

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Closed neighborhood of a vertex set, as a `Finset`. -/
def closedN (G : SimpleGraph α) [DecidableRel G.Adj] (M : Finset α) : Finset α :=
  M ∪ M.biUnion fun w => G.neighborFinset w

lemma mem_closedN {G : SimpleGraph α} [DecidableRel G.Adj] {M : Finset α} {x : α} :
    x ∈ closedN G M ↔ x ∈ M ∨ ∃ w ∈ M, G.Adj w x := by
  simp [closedN, mem_neighborFinset]

lemma subset_closedN {G : SimpleGraph α} [DecidableRel G.Adj] {M : Finset α} :
    M ⊆ closedN G M := fun _ hx => (mem_closedN.mpr (Or.inl hx))

lemma closedN_mono {G : SimpleGraph α} [DecidableRel G.Adj] {M M' : Finset α}
    (h : M ⊆ M') : closedN G M ⊆ closedN G M' := by
  intro x hx
  rcases mem_closedN.mp hx with hx | ⟨w, hw, hadj⟩
  · exact mem_closedN.mpr (Or.inl (h hx))
  · exact mem_closedN.mpr (Or.inr ⟨w, h hw, hadj⟩)

lemma closedN_eq_univ_iff {G : SimpleGraph α} [DecidableRel G.Adj] {M : Finset α} :
    closedN G M = univ ↔ ∀ v : α, v ∈ M ∨ ∃ w ∈ M, G.Adj v w := by
  constructor
  · intro h v
    have := mem_closedN (M := M) (x := v) |>.mp (h ▸ mem_univ v)
    rcases this with hv | ⟨w, hw, hadj⟩
    · exact Or.inl hv
    · exact Or.inr ⟨w, hw, hadj.symm⟩
  · intro h
    ext v
    simp only [mem_univ, iff_true]
    rcases h v with hv | ⟨w, hw, hadj⟩
    · exact mem_closedN.mpr (Or.inl hv)
    · exact mem_closedN.mpr (Or.inr ⟨w, hw, hadj.symm⟩)

/-- A maximum independent set in the open neighbourhood of `v`. -/
lemma exists_indepNeighbors (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    ∃ s : Finset α,
      (s : Set α) ⊆ G.neighborSet v ∧
      G.IsIndepSet (s : Set α) ∧
      s.card = indepNeighborsCard G v := by
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  refine ⟨s.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := mem_map.mp hx
    exact hy
  · intro a ha b hb hab
    obtain ⟨⟨a', haN⟩, ha', rfl⟩ := mem_map.mp ha
    obtain ⟨⟨b', hbN⟩, hb', rfl⟩ := mem_map.mp hb
    have hne : (⟨a', haN⟩ : {x // x ∈ G.neighborSet v}) ≠ ⟨b', hbN⟩ := by
      intro h
      exact hab (congrArg Subtype.val h)
    exact hs.isIndepSet (mem_coe.mpr ha') (mem_coe.mpr hb') hne
  · rw [card_map, hs.card_eq, indepNeighborsCard]

lemma indepNeighborsCard_le_indepNum (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    indepNeighborsCard G v ≤ G.indepNum := by
  obtain ⟨s, _, hindep, hcard⟩ := exists_indepNeighbors G v
  exact hcard ▸ hindep.card_le_indepNum

lemma one_le_indepNeighborsCard [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (v : α) : 1 ≤ indepNeighborsCard G v := by
  have hdeg : 0 < G.degree v := hG.preconnected.degree_pos_of_nontrivial v
  rw [degree_pos_iff_exists_adj] at hdeg
  obtain ⟨w, hw⟩ := hdeg
  let t : Finset {x // x ∈ G.neighborSet v} := {⟨w, hw⟩}
  have hindep : (G.induce (G.neighborSet v)).IsIndepSet (t : Set _) := by
    intro a ha b hb hne
    simp [t] at ha hb
    exact (hne (ha.trans hb.symm)).elim
  have hcard : t.card = 1 := by simp [t]
  have := hindep.card_le_indepNum
  simpa [indepNeighborsCard, hcard] using this

lemma induce_singleton_connected (G : SimpleGraph α) (v : α) :
    (G.induce ({v} : Set α)).Connected :=
  Connected.of_subsingleton

lemma induce_insert_adj {G : SimpleGraph α} {s : Set α} {u v : α}
    (hs : (G.induce s).Connected) (hu : u ∈ s) (huv : G.Adj u v) :
    (G.induce (insert v s)).Connected := by
  by_cases hv : v ∈ s
  · rwa [Set.insert_eq_of_mem hv]
  · have hpair : (G.induce ({u, v} : Set α)).Connected :=
      induce_pair_connected_of_adj huv
    have hunion :=
      induce_union_connected hs.preconnected hpair.preconnected
        ⟨u, ⟨hu, by simp⟩⟩
    have : (insert v s : Set α) = s ∪ {u, v} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | hx)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl hx
      · rintro (hx | rfl | rfl)
        · exact Or.inr hx
        · exact Or.inr hu
        · exact Or.inl rfl
    rwa [this]

lemma induce_star_connected {G : SimpleGraph α} {c : α} {S : Finset α}
    (hS : ∀ s ∈ S, G.Adj c s) :
    (G.induce (insert c S : Set α)).Connected := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [coe_empty]
    have : (insert c (∅ : Set α)) = ({c} : Set α) := by simp
    rw [this]
    exact induce_singleton_connected G c
  | insert a s ha ih =>
    have hadj : G.Adj c a := hS a (mem_insert_self _ _)
    have ih' := ih fun x hx => hS x (mem_insert_of_mem hx)
    rw [coe_insert, Set.insert_comm]
    exact induce_insert_adj ih' (Set.mem_insert c _) hadj

/-- Feasible DeLaVina–Fajtlowicz–Waller pair: independent `M` inside a connected
trunk `T`, with the paper's cardinality invariant rewritten without truncated
natural subtraction. -/
def Feasible (G : SimpleGraph α) [DecidableRel G.Adj] (μ : ℕ)
    (M T : Finset α) : Prop :=
  G.IsIndepSet (M : Set α) ∧
  M ⊆ T ∧
  (G.induce (T : Set α)).Connected ∧
  T ⊆ closedN G M ∧
  T.card + μ ≤ 2 * M.card + 1

lemma feasible_seed (G : SimpleGraph α) [DecidableRel G.Adj] {c : α} {S : Finset α}
    (hSsub : (S : Set α) ⊆ G.neighborSet c)
    (hSindep : G.IsIndepSet (S : Set α))
    (hScard : S.card = indepNeighborsCard G c)
    (hμ : 1 ≤ indepNeighborsCard G c)
    (hc_not_mem : c ∉ S) :
    Feasible G (indepNeighborsCard G c) S (insert c S) := by
  have hAdj : ∀ s ∈ S, G.Adj c s := by
    intro s hs
    exact (mem_neighborSet _ _ _).1 (hSsub hs)
  have hconn : (G.induce (insert c S : Set α)).Connected := induce_star_connected hAdj
  rw [← coe_insert] at hconn
  refine ⟨hSindep, subset_insert _ _, hconn, ?_, ?_⟩
  · intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · have hSne : S.Nonempty := by
        rw [← card_pos, hScard]
        exact hμ
      obtain ⟨s, hs⟩ := hSne
      exact mem_closedN.mpr (Or.inr ⟨s, hs, (hAdj s hs).symm⟩)
    · exact subset_closedN hx
  · have hTcard : (insert c S).card = S.card + 1 := card_insert_of_notMem hc_not_mem
    rw [hTcard, hScard]
    omega

lemma feasible_insert_two {G : SimpleGraph α} [DecidableRel G.Adj] {T : Finset α} {u v : α}
    (hT : (G.induce (T : Set α)).Connected)
    (hm : ∃ m ∈ T, G.Adj m u) (huv : G.Adj u v) :
    (G.induce (insert v (insert u T) : Set α)).Connected := by
  obtain ⟨m, hmT, hmu⟩ := hm
  have hTu : (G.induce (insert u T : Set α)).Connected :=
    induce_insert_adj hT hmT hmu
  simpa [coe_insert] using
    induce_insert_adj hTu (Set.mem_insert u (T : Set α)) huv

lemma feasible_extend (G : SimpleGraph α) [DecidableRel G.Adj] {μ : ℕ} {M T : Finset α}
    (hF : Feasible G μ M T) {u v : α}
    (huN : ∃ m ∈ M, G.Adj m u) (hvout : v ∉ closedN G M) (huv : G.Adj u v) :
    Feasible G μ (insert v M) (insert v (insert u T)) := by
  rcases hF with ⟨hindep, hsub, hconn, hclosed, hbound⟩
  have hvM : v ∉ M := fun hv => hvout (subset_closedN hv)
  have hindep' : G.IsIndepSet ((insert v M : Finset α) : Set α) := by
    intro a ha b hb hne hadj
    rw [coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hne rfl
    · exact hvout (mem_closedN.mpr (Or.inr ⟨b, hb, hadj.symm⟩))
    · exact hvout (mem_closedN.mpr (Or.inr ⟨a, ha, hadj⟩))
    · exact hindep ha hb hne hadj
  have huT : ∃ m ∈ T, G.Adj m u := by
    obtain ⟨m, hm, hadj⟩ := huN
    exact ⟨m, hsub hm, hadj⟩
  have hconn' : (G.induce (↑(insert v (insert u T)) : Set α)).Connected := by
    have hset : (↑(insert v (insert u T)) : Set α) = insert v (insert u (T : Set α)) := by
      ext x; simp
    rw [hset]
    exact feasible_insert_two hconn huT huv
  have hsub' : insert v M ⊆ insert v (insert u T) := by
    intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_of_mem (hsub hx))
  refine ⟨hindep', hsub', hconn', ?_, ?_⟩
  · intro x hx
    have hmono : closedN G M ⊆ closedN G (insert v M) := closedN_mono (subset_insert _ _)
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact subset_closedN (mem_insert_self _ _)
    · rw [mem_insert] at hx
      rcases hx with rfl | hx
      · obtain ⟨m, hm, hadj⟩ := huN
        exact hmono (mem_closedN.mpr (Or.inr ⟨m, hm, hadj⟩))
      · exact hmono (hclosed hx)
  · have hcardT : (insert v (insert u T)).card ≤ T.card + 2 := by
      calc
        (insert v (insert u T)).card ≤ (insert u T).card + 1 := card_insert_le _ _
        _ ≤ T.card + 1 + 1 := Nat.add_le_add_right (card_insert_le _ _) 1
        _ = T.card + 2 := by omega
    have hcardM : (insert v M).card = M.card + 1 := card_insert_of_notMem hvM
    rw [hcardM]
    omega

lemma exists_boundary_extension (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) {M T : Finset α} (hTne : T.Nonempty)
    (hTsub : T ⊆ closedN G M) (hnot : closedN G M ≠ univ) :
    ∃ u v, (∃ m ∈ M, G.Adj m u) ∧ v ∉ closedN G M ∧ G.Adj u v := by
  obtain ⟨y, hy⟩ : ∃ y, y ∉ closedN G M := by
    contrapose! hnot
    exact eq_univ_iff_forall.2 hnot
  obtain ⟨w0, hw0⟩ := hTne
  obtain ⟨p⟩ := hG.preconnected w0 y
  obtain ⟨d, _, hd1, hd2⟩ :=
    p.exists_boundary_dart (closedN G M : Set α) (hTsub hw0) hy
  have hfst : d.fst ∈ closedN G M := hd1
  have hsnd : d.snd ∉ closedN G M := hd2
  have hfst_not_M : d.fst ∉ M := by
    intro hf
    exact hsnd (mem_closedN.mpr (Or.inr ⟨d.fst, hf, d.adj⟩))
  rcases mem_closedN.mp hfst with hf | ⟨m, hm, hadjm⟩
  · exact (hfst_not_M hf).elim
  · exact ⟨d.fst, d.snd, ⟨m, hm, hadjm⟩, hsnd, d.adj⟩

lemma exists_maximal_feasible (G : SimpleGraph α) [DecidableRel G.Adj]
    (μ : ℕ) {S T0 : Finset α} (hseed : Feasible G μ S T0) :
    ∃ M T, Feasible G μ M T ∧ ∀ M' T', Feasible G μ M' T' → M'.card ≤ M.card := by
  classical
  let P : Finset (Finset α × Finset α) :=
    (univ.powerset.product univ.powerset).filter fun p => Feasible G μ p.1 p.2
  have hPne : P.Nonempty := by
    refine ⟨(S, T0), mem_filter.mpr ⟨?_, hseed⟩⟩
    simp [mem_product, mem_powerset]
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image (fun p => p.1.card) hPne
  exact ⟨p.1, p.2, (mem_filter.mp hp).2, fun M' T' hF =>
    hmax (M', T') (mem_filter.mpr ⟨by simp [mem_product, mem_powerset], hF⟩)⟩

lemma exists_connected_dom_bound [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (μ : ℕ) (hμ : μ = (univ.image fun v => indepNeighborsCard G v).max'
      (by simp)) :
    ∃ T : Finset α, (G.induce (T : Set α)).Connected ∧ closedN G T = univ ∧
      T.card + μ ≤ 2 * G.indepNum + 1 := by
  have hμpos : 1 ≤ μ := by
    obtain ⟨c, hc, hceq⟩ := mem_image.mp (max'_mem (univ.image fun v => indepNeighborsCard G v)
      (by simp))
    have := one_le_indepNeighborsCard G hG c
    rw [hμ, ← hceq]
    exact this
  obtain ⟨c, -, hc⟩ := mem_image.mp (max'_mem (univ.image fun v => indepNeighborsCard G v)
    (by simp))
  have hcμ : indepNeighborsCard G c = μ := hc.trans hμ.symm
  obtain ⟨S, hSsub, hSindep, hScard⟩ := exists_indepNeighbors G c
  have hcS : c ∉ S := fun h =>
    ((mem_neighborSet _ _ _).1 (hSsub h)).ne rfl
  have hseed0 := feasible_seed G hSsub hSindep hScard (hcμ.symm ▸ hμpos) hcS
  have hseed : Feasible G μ S (insert c S) := hcμ ▸ hseed0
  obtain ⟨M, T, hF, hmax⟩ := exists_maximal_feasible G μ hseed
  have hconn := hF.2.2.1
  have hclosed := hF.2.2.2.1
  have hTne : T.Nonempty := by
    obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
    exact ⟨x, hx⟩
  by_cases hdomM : closedN G M = univ
  · have hindep := hF.1
    have hsub := hF.2.1
    have hbound := hF.2.2.2.2
    refine ⟨T, hconn, ?_, ?_⟩
    · exact eq_univ_of_forall fun x => by
        have hx : x ∈ closedN G M := by rw [hdomM]; exact mem_univ x
        rcases mem_closedN.mp hx with hx | ⟨w, hw, hadj⟩
        · exact mem_closedN.mpr (Or.inl (hsub hx))
        · exact mem_closedN.mpr (Or.inr ⟨w, hsub hw, hadj⟩)
    · have hMα : M.card ≤ G.indepNum := hindep.card_le_indepNum
      omega
  · obtain ⟨u, v, huN, hvout, huv⟩ :=
      exists_boundary_extension G hG hTne hclosed hdomM
    have hF' := feasible_extend (G := G) hF huN hvout huv
    have hvM : v ∉ M := fun hv => hvout (subset_closedN hv)
    have : (insert v M).card ≤ M.card := hmax _ _ hF'
    rw [card_insert_of_notMem hvM] at this
    omega

/-- From a connected dominating vertex set, attach each external vertex as a
degree-one leaf of some spanning tree. -/
lemma exists_spanning_tree_leaves (G : SimpleGraph α) [DecidableRel G.Adj]
    (H : G.Subgraph) (hHc : H.Connected)
    (hdom : closedN G H.verts.toFinset = univ) :
    ∃ T : G.Subgraph, T.IsSpanning ∧ T.coe.IsTree ∧
      Fintype.card α ≤
        (T.verts.toFinset.filter fun v => T.degree v = 1).card + H.verts.toFinset.card := by
  classical
  set W : Set α := H.verts
  have hchoice : ∀ x : α, x ∉ W → ∃ w, w ∈ W ∧ G.Adj w x := by
    intro x hx
    have hx' : x ∈ closedN G H.verts.toFinset := by
      rw [hdom]; exact mem_univ x
    rcases mem_closedN.mp hx' with hxW | ⟨w, hw, hadj⟩
    · exact (hx (Set.mem_toFinset.mp hxW)).elim
    · exact ⟨w, Set.mem_toFinset.mp hw, hadj⟩
  choose pend hpendW hpendAdj using hchoice
  let G' : SimpleGraph α :=
    { Adj := fun a b =>
        H.spanningCoe.Adj a b ∨
        (∃ h : a ∉ W, pend a h = b) ∨
        (∃ h : b ∉ W, pend b h = a)
      symm := ⟨by
        intro a b h
        rcases h with h | ⟨ha, e⟩ | ⟨hb, e⟩
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨ha, e⟩)
        · exact Or.inr (Or.inl ⟨hb, e⟩)⟩
      loopless := ⟨by
        intro a h
        rcases h with h | ⟨ha, e⟩ | ⟨hb, e⟩
        · exact h.ne rfl
        · exact ha (e ▸ hpendW a ha)
        · exact hb (e ▸ hpendW a hb)⟩ }
  have hG'le : G' ≤ G := by
    intro a b h
    rcases h with h | ⟨ha, e⟩ | ⟨hb, e⟩
    · exact H.spanningCoe_le h
    · exact e ▸ (hpendAdj a ha).symm
    · exact e ▸ hpendAdj b hb
  obtain ⟨w0, hw0⟩ := hHc.nonempty
  have hinW : ∀ x, x ∈ W → G'.Reachable x w0 := by
    intro x hx
    have hr : H.coe.Reachable ⟨x, hx⟩ ⟨w0, hw0⟩ := hHc.coe.preconnected _ _
    exact hr.map ⟨Subtype.val, fun {a b} hab => Or.inl hab⟩
  have hreach : ∀ x, G'.Reachable x w0 := by
    intro x
    by_cases hx : x ∈ W
    · exact hinW x hx
    · have hadj : G'.Adj x (pend x hx) := Or.inr (Or.inl ⟨hx, rfl⟩)
      exact hadj.reachable.trans (hinW _ (hpendW x hx))
  have hG'conn : G'.Connected := by
    haveI : Nonempty α := ⟨w0⟩
    exact ⟨fun a b => (hreach a).trans (hreach b).symm⟩
  have hpendNbhd : ∀ (x : α) (hx : x ∉ W), G'.neighborFinset x = {pend x hx} := by
    intro x hx
    ext z
    simp only [mem_neighborFinset, mem_singleton]
    constructor
    · rintro (h | ⟨hx', e⟩ | ⟨hz, e⟩)
      · exact (hx (H.edge_vert h)).elim
      · exact e.symm
      · exact (hx (e ▸ hpendW z hz)).elim
    · rintro rfl
      exact Or.inr (Or.inl ⟨hx, rfl⟩)
  obtain ⟨T', hT'le, hT'tree⟩ := hG'conn.exists_isTree_le
  have hT'leG : T' ≤ G := hT'le.trans hG'le
  refine ⟨toSubgraph T' hT'leG, toSubgraph.isSpanning T' hT'leG, ?_, ?_⟩
  · let e : (toSubgraph T' hT'leG).coe ≃g T' :=
      { toEquiv := Equiv.Set.univ α
        map_rel_iff' := Iff.rfl }
    exact (Iso.isTree_iff e).mpr hT'tree
  · have hleaf : ∀ (x : α), x ∉ W → (toSubgraph T' hT'leG).degree x = 1 := by
      intro x hx
      rw [degree_toSubgraph]
      have hle1 : T'.degree x ≤ 1 := by
        have hsub : T'.neighborFinset x ⊆ G'.neighborFinset x := by
          intro z hz
          rw [mem_neighborFinset] at hz ⊢
          exact hT'le hz
        calc
          T'.degree x = (T'.neighborFinset x).card := rfl
          _ ≤ (G'.neighborFinset x).card := card_le_card hsub
          _ = 1 := by rw [hpendNbhd x hx, card_singleton]
      haveI : Nontrivial α := ⟨⟨x, w0, fun h => hx (h ▸ hw0)⟩⟩
      have hge1 : 0 < T'.degree x :=
        hT'tree.connected.preconnected.degree_pos_of_nontrivial x
      omega
    have hcover : (univ : Finset α) ⊆
        ((toSubgraph T' hT'leG).verts.toFinset.filter
          fun v => (toSubgraph T' hT'leG).degree v = 1) ∪
        H.verts.toFinset := by
      intro x _
      by_cases hx : x ∈ W
      · exact mem_union_right _ (Set.mem_toFinset.mpr hx)
      · refine mem_union_left _ (mem_filter.mpr ⟨?_, hleaf x hx⟩)
        simp [Set.mem_toFinset]
    calc
      Fintype.card α = (univ : Finset α).card := card_univ.symm
      _ ≤ _ := card_le_card hcover
      _ ≤ _ := card_union_le _ _

lemma le_Ls_of_leaves (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : G.Subgraph) (hsp : T.IsSpanning) (htree : T.coe.IsTree)
    {k : ℕ} (hk : k ≤ (T.verts.toFinset.filter fun v => T.degree v = 1).card) :
    (k : ℝ) ≤ Ls G := by
  classical
  let spanningTrees : Set G.Subgraph := { T | T.IsSpanning ∧ T.coe.IsTree }
  let num (T : G.Subgraph) : ℕ :=
    (T.verts.toFinset.filter fun v => T.degree v = 1).card
  have hLs : Ls G = sSup (Set.image (fun T => (num T : ℝ)) spanningTrees) := rfl
  rw [hLs]
  have hbdd : BddAbove (Set.image (fun T => (num T : ℝ)) spanningTrees) := by
    refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro _ ⟨T, _, rfl⟩
    exact Nat.cast_le.mpr (card_le_univ _)
  have hmem : (num T : ℝ) ∈ Set.image (fun T => (num T : ℝ)) spanningTrees :=
    ⟨T, ⟨hsp, htree⟩, rfl⟩
  exact (Nat.cast_le.2 hk).trans (le_csSup hbdd hmem)

/-- The frozen WOWII7 bound. -/
theorem conjecture7 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (univ.image fun v => indepNeighborsCard G v).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  intro maxL
  let μ := maxL
  obtain ⟨Tdom, hconn, hdom, hbound⟩ := exists_connected_dom_bound G h μ rfl
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (Tdom : Set α)
  have hHc : H.Connected := by
    rw [← connected_induce_iff]
    exact hconn
  have hverts : H.verts.toFinset = Tdom := by
    simp [H]
  have hdom' : closedN G H.verts.toFinset = univ := by
    simpa [hverts] using hdom
  obtain ⟨T, hsp, htree, hcount⟩ := exists_spanning_tree_leaves G H hHc hdom'
  have hk : Fintype.card α - Tdom.card ≤
      (T.verts.toFinset.filter fun v => T.degree v = 1).card := by
    have hle : Tdom.card ≤ Fintype.card α := Tdom.card_le_univ
    have : Fintype.card α ≤
        (T.verts.toFinset.filter fun v => T.degree v = 1).card + Tdom.card := by
      simpa [hverts] using hcount
    omega
  have hLs : ((Fintype.card α - Tdom.card : ℕ) : ℝ) ≤ Ls G :=
    le_Ls_of_leaves G T hsp htree hk
  have hint :
      ((μ : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ)) ≤
        ((Fintype.card α - Tdom.card : ℕ) : ℤ) := by
    have hle : Tdom.card ≤ Fintype.card α := Tdom.card_le_univ
    have : (Fintype.card α - Tdom.card : ℕ) = Fintype.card α - Tdom.card := rfl
    have hsub : ((Fintype.card α - Tdom.card : ℕ) : ℤ) =
        (Fintype.card α : ℤ) - Tdom.card := Int.ofNat_sub hle
    have : (Tdom.card : ℤ) + μ ≤ 2 * (G.indepNum : ℤ) + 1 := by exact_mod_cast hbound
    linarith
  have hintR :
      ((μ : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤
        ((Fintype.card α - Tdom.card : ℕ) : ℝ) := by exact_mod_cast hint
  exact hintR.trans hLs

end WOWII7

#print axioms WOWII7.conjecture7
#check WOWII7.conjecture7
