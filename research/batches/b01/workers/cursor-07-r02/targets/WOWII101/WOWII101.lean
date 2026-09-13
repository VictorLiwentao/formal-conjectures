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

Original statement formalization: The Formal Conjectures Authors.
New independent Lean development and write-up: Wentao Li.
Mathematics: András Hajnal (1965); independent-set form and core/corona
language as in Levit–Mandrescu, arXiv:1101.4564, Corollaries 2.3–2.4.
-/
import FormalConjectures.WrittenOnTheWallII.GraphConjecture101

/-!
Independent Lean proof of WOWII Graph Conjecture 101 (Hajnal independence-core
inequality). This file imports the frozen source only for the definitions
`indepNumDeleteVertex` and `alphaCore`. It does not apply the admitted
`WrittenOnTheWallII.GraphConjecture101.conjecture101`.

Classification: known_mathematics_formalization, not new mathematics.
-/

set_option linter.unusedSectionVars false
set_option linter.style.moduleDocstring false
set_option autoImplicit false

open SimpleGraph Finset Function

namespace WOWII101

open WrittenOnTheWallII.GraphConjecture101

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

lemma compl_induce (s : Set α) : (G.induce s)ᶜ = Gᶜ.induce s := by
  ext x y
  simp [compl_adj, Subtype.ext_iff]

lemma isNIndepSet_induce_iff {s : Set α} {t : Finset s} {n : ℕ} :
    (G.induce s).IsNIndepSet n t ↔ G.IsNIndepSet n (t.map (.subtype _)) := by
  rw [← isNClique_compl, compl_induce, isNClique_induce_iff, isNClique_compl]

lemma indepNum_induce_le (s : Set α) : (G.induce s).indepNum ≤ G.indepNum := by
  obtain ⟨t, ht⟩ := exists_isNIndepSet_indepNum (G := G.induce s)
  have hG : G.IsNIndepSet (G.induce s).indepNum (t.map (.subtype _)) :=
    (isNIndepSet_induce_iff G (s := s)).1 ht
  have hle := hG.isIndepSet.card_le_indepNum
  rwa [card_map, ht.card_eq] at hle

lemma not_mem_map_univ_sdiff_singleton (v : α)
    (t : Finset {x // x ∈ (Set.univ \ {v} : Set α)}) :
    v ∉ t.map (.subtype _) := by
  intro hv
  obtain ⟨⟨x, hx⟩, _, hxv⟩ := mem_map.mp hv
  have hxeq : x = v := hxv
  simp [Set.mem_sdiff] at hx
  exact hx hxeq

lemma isIndepSet_subset {s t : Set α} (h : s ⊆ t) (ht : G.IsIndepSet t) :
    G.IsIndepSet s := by
  rw [← isClique_compl] at ht ⊢
  exact ht.subset h

lemma isIndepSet_union {A B : Set α} (hA : G.IsIndepSet A) (hB : G.IsIndepSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : G.IsIndepSet (A ∪ B) := by
  intro x hx y hy hxy
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · exact hA hxA hyA hxy
    · exact hAB x hxA y hyB
  · rcases hy with hyA | hyB
    · exact fun h => hAB y hyA x hxB h.symm
    · exact hB hxB hyB hxy

lemma card_inter_add_sdiff (s t : Finset α) :
    (s ∩ t).card + (s \ t).card = s.card := by
  have hunion : s ∩ t ∪ s \ t = s := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hd : Disjoint (s ∩ t) (s \ t) := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp
  calc
    (s ∩ t).card + (s \ t).card = (s ∩ t ∪ s \ t).card :=
      (card_union_of_disjoint hd).symm
    _ = s.card := by rw [hunion]

lemma card_union_eq_right_add_sdiff (s t : Finset α) :
    (s ∪ t).card = t.card + (s \ t).card := by
  have hunion : t ∪ (s \ t) = s ∪ t := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  have hd : Disjoint t (s \ t) := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp
  calc
    (s ∪ t).card = (t ∪ (s \ t)).card := by rw [hunion]
    _ = t.card + (s \ t).card := card_union_of_disjoint hd

lemma card_slice_identity (I S U : Finset α) (hIU : I ⊆ U) :
    (I ∪ (S ∩ U)).card + (S \ U).card = S.card + (I \ S).card := by
  have hinter : I ∩ (S ∩ U) = I ∩ S := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hIU h.1⟩⟩
  have hunion := card_union_add_card_inter I (S ∩ U)
  rw [hinter] at hunion
  have hI := card_inter_add_sdiff I S
  have hS := card_inter_add_sdiff S U
  omega

noncomputable def maxIndepSets : Finset (Finset α) :=
  G.indepSetFinset G.indepNum

lemma maxIndepSets_nonempty : (maxIndepSets G).Nonempty := by
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G)
  exact ⟨s, mem_indepSetFinset_iff.2 hs⟩

lemma mem_maxIndepSets_iff {s : Finset α} :
    s ∈ maxIndepSets G ↔ G.IsNIndepSet G.indepNum s :=
  mem_indepSetFinset_iff

lemma indepNumDeleteVertex_le (v : α) :
    indepNumDeleteVertex G v ≤ G.indepNum :=
  indepNum_induce_le G (Set.univ \ {v})

lemma mem_alphaCore_iff (v : α) :
    v ∈ alphaCore G ↔ ∀ s, G.IsNIndepSet G.indepNum s → v ∈ s := by
  constructor
  · intro hv s hs
    simp only [alphaCore, mem_filter, mem_univ, true_and] at hv
    by_contra hvns
    have hmem : ∀ x ∈ s, x ∈ (Set.univ \ {v} : Set α) := by
      intro x hx
      simp [Set.mem_sdiff]
      rintro rfl
      exact hvns hx
    have hs' : (G.induce (Set.univ \ {v})).IsNIndepSet G.indepNum
        (s.subtype fun x => x ∈ (Set.univ \ {v} : Set α)) := by
      rw [isNIndepSet_induce_iff, subtype_map_of_mem hmem]
      exact hs
    have : G.indepNum ≤ indepNumDeleteVertex G v := by
      simpa [indepNumDeleteVertex, hs'.card_eq] using hs'.isIndepSet.card_le_indepNum
    exact (Nat.not_lt.mpr this) hv
  · intro hall
    simp only [alphaCore, mem_filter, mem_univ, true_and]
    have hle := indepNumDeleteVertex_le G v
    refine lt_of_le_of_ne hle fun heq => ?_
    let H := G.induce (Set.univ \ {v})
    obtain ⟨t, ht⟩ := exists_isNIndepSet_indepNum (G := H)
    have hG : G.IsNIndepSet (indepNumDeleteVertex G v) (t.map (.subtype _)) :=
      (isNIndepSet_induce_iff G (s := (Set.univ \ {v} : Set α))).1 ht
    have hmax : G.IsNIndepSet G.indepNum (t.map (.subtype _)) := by
      convert hG
      exact heq.symm
    exact not_mem_map_univ_sdiff_singleton v t (hall _ hmax)

lemma alphaCore_eq_inf_maxIndepSets :
    alphaCore G = (maxIndepSets G).inf' (maxIndepSets_nonempty G) (fun s => s) := by
  ext v
  simp only [mem_alphaCore_iff, mem_inf', mem_maxIndepSets_iff]

lemma isIndepSet_inf_union_slice (F' : Finset (Finset α)) (hne' : F'.Nonempty)
    (hmax : ∀ s ∈ F', G.IsNIndepSet G.indepNum s) {S : Finset α}
    (hS : G.IsNIndepSet G.indepNum S) :
    G.IsIndepSet
      (↑(F'.inf' hne' (fun t => t) ∪ (S ∩ F'.sup' hne' (fun t => t))) : Set α) := by
  let I := F'.inf' hne' (fun t => t)
  let U := F'.sup' hne' (fun t => t)
  let T := I ∪ (S ∩ U)
  have hI : G.IsIndepSet (I : Set α) := by
    obtain ⟨W, hW⟩ := show ∃ x, x ∈ F' from hne'
    refine isIndepSet_subset G (s := (I : Set α)) (t := (W : Set α)) ?_
      (hmax W hW).isIndepSet
    intro x hx
    exact (mem_inf' (f := fun t : Finset α => t) hne').1 hx W hW
  have hSU : G.IsIndepSet ((S ∩ U : Finset α) : Set α) :=
    isIndepSet_subset G (s := ((S ∩ U : Finset α) : Set α)) (t := (S : Set α))
      (fun x hx => (mem_inter.1 hx).1) hS.isIndepSet
  change G.IsIndepSet (T : Set α)
  rw [coe_union]
  refine isIndepSet_union G hI hSU ?_
  intro a ha b hb
  have haI : a ∈ I := ha
  have hbU : b ∈ U := (mem_inter.1 hb).2
  obtain ⟨W, hW, hbW⟩ := (mem_sup' (f := fun t : Finset α => t) hne').1 hbU
  have haW : a ∈ W := (mem_inf' (f := fun t : Finset α => t) hne').1 haI W hW
  by_cases hab : a = b
  · subst hab
    exact fun h => SimpleGraph.irrefl G h
  · exact (hmax W hW).isIndepSet haW hbW hab

lemma two_mul_indepNum_le_inf_add_sup (F : Finset (Finset α)) :
    ∀ (hne : F.Nonempty), (∀ s ∈ F, G.IsNIndepSet G.indepNum s) →
      2 * G.indepNum ≤ (F.inf' hne (fun s => s)).card +
        (F.sup' hne (fun s => s)).card := by
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hne hmax
    obtain ⟨S, hS⟩ := show ∃ x, x ∈ F from hne
    by_cases hne' : (F.erase S).Nonempty
    · have hss : F.erase S ⊂ F := erase_ssubset hS
      have ih' := ih (F.erase S) hss hne' fun t hs => hmax t (mem_of_mem_erase hs)
      let I := (F.erase S).inf' hne' (fun t => t)
      let U := (F.erase S).sup' hne' (fun t => t)
      have hinf : F.inf' hne (fun s => s) = S ∩ I := by
        ext x
        constructor
        · intro hx
          have hxF := (mem_inf' (f := fun s : Finset α => s) hne).1 hx
          refine mem_inter.2 ⟨hxF S hS, (mem_inf' (f := fun t : Finset α => t) hne').2 ?_⟩
          intro t ht
          exact hxF t (mem_of_mem_erase ht)
        · intro hx
          refine (mem_inf' (f := fun s : Finset α => s) hne).2 ?_
          intro t ht
          by_cases htS : t = S
          · subst htS
            exact (mem_inter.1 hx).1
          · exact (mem_inf' (f := fun t : Finset α => t) hne').1 (mem_inter.1 hx).2 t
              (mem_erase.2 ⟨htS, ht⟩)
      have hsup : F.sup' hne (fun s => s) = S ∪ U := by
        ext x
        constructor
        · intro hx
          obtain ⟨t, ht, hxt⟩ := (mem_sup' (f := fun s : Finset α => s) hne).1 hx
          by_cases htS : t = S
          · subst htS
            exact mem_union.2 (Or.inl hxt)
          · exact mem_union.2 (Or.inr ((mem_sup' (f := fun t : Finset α => t) hne').2
              ⟨t, mem_erase.2 ⟨htS, ht⟩, hxt⟩))
        · intro hx
          refine (mem_sup' (f := fun s : Finset α => s) hne).2 ?_
          rcases mem_union.1 hx with hxS | hxU
          · exact ⟨S, hS, hxS⟩
          · obtain ⟨t, ht, hxt⟩ := (mem_sup' (f := fun t : Finset α => t) hne').1 hxU
            exact ⟨t, mem_of_mem_erase ht, hxt⟩
      have hIU : I ⊆ U := by
        intro x hx
        obtain ⟨W, hW⟩ := show ∃ x, x ∈ F.erase S from hne'
        exact (mem_sup' (f := fun t : Finset α => t) hne').2
          ⟨W, hW, (mem_inf' (f := fun t : Finset α => t) hne').1 hx W hW⟩
      have hT : G.IsIndepSet (↑(I ∪ (S ∩ U)) : Set α) := by
        simpa [I, U] using
          isIndepSet_inf_union_slice G (F.erase S) hne'
            (fun t hs => hmax t (mem_of_mem_erase hs)) (hmax S hS)
      have hTle : (I ∪ (S ∩ U)).card ≤ G.indepNum := hT.card_le_indepNum
      have hScard : S.card = G.indepNum := (hmax S hS).card_eq
      have hid := card_slice_identity I S U hIU
      have hloss : (I \ S).card ≤ (S \ U).card := by
        have : (I ∪ (S ∩ U)).card ≤ S.card := by simpa [hScard] using hTle
        omega
      have hIpart := card_inter_add_sdiff I S
      have hUpart := card_union_eq_right_add_sdiff S U
      have hge : I.card + U.card ≤ (S ∩ I).card + (S ∪ U).card := by
        have hSI : (S ∩ I).card = (I ∩ S).card := by rw [inter_comm]
        omega
      have hfinal : 2 * G.indepNum ≤ (S ∩ I).card + (S ∪ U).card :=
        le_trans ih' hge
      simpa [hinf, hsup] using hfinal
    · have hF : F = {S} := by
        rw [← insert_erase hS, not_nonempty_iff_eq_empty.mp hne']
        simp
      have hScard : S.card = G.indepNum := (hmax S hS).card_eq
      simp [hF, inf'_singleton, sup'_singleton, hScard, Nat.two_mul]

lemma two_mul_indepNum_le_card_add_alphaCore :
    2 * G.indepNum ≤ Fintype.card α + (alphaCore G).card := by
  let Ω := maxIndepSets G
  have hΩ : Ω.Nonempty := maxIndepSets_nonempty G
  have hmax : ∀ s ∈ Ω, G.IsNIndepSet G.indepNum s := fun s hs =>
    (mem_maxIndepSets_iff G).1 hs
  have hfam := two_mul_indepNum_le_inf_add_sup G Ω hΩ hmax
  have hcore : (Ω.inf' hΩ (fun s => s)).card = (alphaCore G).card := by
    rw [alphaCore_eq_inf_maxIndepSets]
  have hsuple : (Ω.sup' hΩ (fun s => s)).card ≤ Fintype.card α := card_le_univ _
  calc
    2 * G.indepNum ≤ (Ω.inf' hΩ (fun s => s)).card + (Ω.sup' hΩ (fun s => s)).card :=
      hfam
    _ ≤ (Ω.inf' hΩ (fun s => s)).card + Fintype.card α := Nat.add_le_add_left hsuple _
    _ = (alphaCore G).card + Fintype.card α := by rw [hcore]
    _ = Fintype.card α + (alphaCore G).card := Nat.add_comm _ _

/-- Exact frozen proposition of `WrittenOnTheWallII.GraphConjecture101.conjecture101`. -/
theorem conjecture101 (_h : G.Connected) :
    G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2 := by
  rw [Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 2)]
  simpa [Nat.mul_comm] using two_mul_indepNum_le_card_add_alphaCore G

example {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    G.indepNum ≤ (Fintype.card α + (WrittenOnTheWallII.GraphConjecture101.alphaCore G).card) / 2 :=
  conjecture101 G h

end WOWII101

#print axioms WOWII101.conjecture101
#check WrittenOnTheWallII.GraphConjecture101.conjecture101
#check WOWII101.conjecture101
