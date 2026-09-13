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

open SimpleGraph Finset

namespace WOWII101

open WrittenOnTheWallII.GraphConjecture101

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable (G : SimpleGraph α) [DecidableRel G.Adj]

lemma compl_induce (s : Set α) : (G.induce s)ᶜ = Gᶜ.induce s := by
  ext x y
  simp [compl_adj, induce_adj]

lemma isNIndepSet_induce_iff {s : Set α} {t : Finset s} {n : ℕ} :
    (G.induce s).IsNIndepSet n t ↔ G.IsNIndepSet n (t.map (.subtype _)) := by
  rw [← isNClique_compl, compl_induce, isNClique_induce_iff, isNClique_compl]

lemma indepNum_induce_le (s : Set α) : (G.induce s).indepNum ≤ G.indepNum := by
  obtain ⟨t, ht⟩ := (G.induce s).exists_isNIndepSet_indepNum
  have hG : G.IsNIndepSet (G.induce s).indepNum (t.map (.subtype _)) :=
    (isNIndepSet_induce_iff (s := s)).1 ht
  simpa [hG.card_eq, card_map] using hG.isIndepSet.card_le_indepNum

lemma not_mem_map_univ_diff_singleton (v : α)
    (t : Finset {x // x ∈ (Set.univ \ {v} : Set α)}) :
    v ∉ t.map (Embedding.subtype _) := by
  intro hv
  obtain ⟨⟨x, hx⟩, _, rfl⟩ := mem_map.mp hv
  simp [Set.mem_diff] at hx

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

private def maxFamily : Finset (Finset α) := G.indepSetFinset G.indepNum

lemma maxFamily_nonempty : (G.maxFamily).Nonempty := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨s, mem_indepSetFinset_iff.2 hs⟩

lemma mem_maxFamily_iff {s : Finset α} :
    s ∈ G.maxFamily ↔ G.IsNIndepSet G.indepNum s :=
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
    have hs' : (G.induce (Set.univ \ {v})).IsNIndepSet G.indepNum
        (s.subtype fun x => x ∈ (Set.univ \ {v} : Set α)) := by
      rw [isNIndepSet_induce_iff]
      convert hs
      refine subtype_map_of_mem fun x hx => ?_
      simp [Set.mem_diff]
      rintro rfl
      exact hvns hx
    have : G.indepNum ≤ indepNumDeleteVertex G v := by
      simpa [indepNumDeleteVertex, hs'.card_eq] using
        hs'.isIndepSet.card_le_indepNum
    exact (Nat.not_lt.mpr this) hv
  · intro hall
    simp only [alphaCore, mem_filter, mem_univ, true_and]
    have hle := indepNumDeleteVertex_le G v
    refine lt_of_le_of_ne hle fun heq => ?_
    obtain ⟨t, ht⟩ := (G.induce (Set.univ \ {v})).exists_isNIndepSet_indepNum
    have hG : G.IsNIndepSet (indepNumDeleteVertex G v)
        (t.map (Embedding.subtype _)) := (isNIndepSet_induce_iff).1 ht
    have hvnot := not_mem_map_univ_diff_singleton v t
    have hmax : G.IsNIndepSet G.indepNum (t.map (Embedding.subtype _)) := by
      rw [← heq]
      exact hG
    exact hvnot (hall _ hmax)

lemma alphaCore_eq_inf_maxFamily :
    alphaCore G = (G.maxFamily).inf' (G.maxFamily_nonempty) (fun s => s) := by
  ext v
  simp [mem_alphaCore_iff, mem_inf', G.mem_maxFamily_iff]

lemma card_inter_eq_card_sub_sdiff (I S : Finset α) :
    (I ∩ S).card = I.card - (I \ S).card := by
  have hsub : I \ S ⊆ I := sdiff_subset
  have := card_sdiff_add_card_eq_card (s := I ∩ S) (t := I) (by intro x hx; exact (mem_inter.mp hx).1)
  have hinter : I ∩ S ∪ (I \ S) = I := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hdisj : Disjoint (I ∩ S) (I \ S) := disjoint_sdiff
  rw [← hinter, card_union_of_disjoint hdisj] at this
  -- `this` is not the identity we want; prove directly.
  have h' : (I ∩ S).card + (I \ S).card = I.card := by
    rw [← card_union_of_disjoint hdisj, hinter]
  omega

lemma card_slice_identity (I S U : Finset α) (hIU : I ⊆ U) :
    (I ∪ (S ∩ U)).card + (S \ U).card = S.card + (I \ S).card := by
  have hIU' : I ∩ (S ∩ U) = I ∩ S := by
    ext x
    simp only [mem_inter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hIU h.1⟩
  have hunion : (I ∪ (S ∩ U)).card + (I ∩ (S ∩ U)).card = I.card + (S ∩ U).card :=
    card_union_add_card_inter _ _
  have hSU : (S ∩ U).card + (S \ U).card = S.card := by
    have : S ∩ U ∪ (S \ U) = S := by
      ext x
      simp only [mem_union, mem_inter, mem_sdiff]
      tauto
    have hdisj : Disjoint (S ∩ U) (S \ U) := by
      intro x hx
      simp [mem_inter, mem_sdiff] at hx
    rw [← this, card_union_of_disjoint (by
      intro x hx
      simp [inf_eq_inter, mem_inter, mem_sdiff] at hx ⊢
      exact hx.2.2 hx.1.2)]
  have hI : I.card = (I ∩ S).card + (I \ S).card := by
    have hinter : I ∩ S ∪ (I \ S) = I := by
      ext x
      simp only [mem_union, mem_inter, mem_sdiff]
      tauto
    have hdisj : Disjoint (I ∩ S) (I \ S) := disjoint_sdiff
    rw [← hinter, card_union_of_disjoint hdisj]
  rw [hIU'] at hunion
  omega

lemma isIndepSet_inf_union_slice (F' : Finset (Finset α)) (hne' : F'.Nonempty)
    (hmax : ∀ s ∈ F', G.IsNIndepSet G.indepNum s) (S : Finset α)
    (hS : G.IsNIndepSet G.indepNum S) :
    G.IsIndepSet
      ((F'.inf' hne' (fun t => t) ∪ (S ∩ F'.sup' hne' (fun t => t)) : Finset α) : Set α) := by
  set I := F'.inf' hne' (fun t => t)
  set U := F'.sup' hne' (fun t => t)
  have hI : G.IsIndepSet (I : Set α) := by
    obtain ⟨W, hW⟩ := hne'
    refine isIndepSet_subset G ?_ (hmax W hW).isIndepSet
    intro x hx
    have hxI : x ∈ I := by exact_mod_cast hx
    have : ∀ t ∈ F', x ∈ t := (mem_inf' hne').1 hxI
    exact this W hW
  have hSset : G.IsIndepSet ((S ∩ U : Finset α) : Set α) :=
    isIndepSet_subset G (by intro x hx; exact (mem_inter.mp (by exact_mod_cast hx)).1)
      hS.isIndepSet
  refine isIndepSet_union G hI hSset ?_
  intro a ha b hb hab
  have haI : a ∈ I := by exact_mod_cast ha
  have hbSU : b ∈ S ∩ U := by exact_mod_cast hb
  have hbU : b ∈ U := (mem_inter.mp hbSU).2
  obtain ⟨W, hW, hbW⟩ := (mem_sup' hne').1 hbU
  have haW : a ∈ W := (mem_inf' hne').1 haI W hW
  have hWind : G.IsIndepSet (W : Set α) := (hmax W hW).isIndepSet
  exact hWind haW hbW hab

lemma two_mul_indepNum_le_inf_add_sup (F : Finset (Finset α)) :
    ∀ (hne : F.Nonempty), (∀ s ∈ F, G.IsNIndepSet G.indepNum s) →
      2 * G.indepNum ≤ (F.inf' hne (fun s => s)).card + (F.sup' hne (fun s => s)).card := by
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hne hmax
    obtain ⟨S, hS⟩ := hne
    set F' := F.erase S
    by_cases hne' : F'.Nonempty
    · have hss : F' ⊂ F := erase_ssubset hS
      have ih' := ih F' hss hne' fun t hs => hmax t (mem_of_mem_erase hs)
      set I := F'.inf' hne' (fun t => t)
      set U := F'.sup' hne' (fun t => t)
      have hinf : F.inf' hne (fun s => s) = S ∩ I := by
        ext x
        simp only [mem_inter, mem_inf']
        constructor
        · intro hx
          exact ⟨hx S hS, fun t ht => hx t (mem_of_mem_erase ht)⟩
        · intro hx t ht
          by_cases hts : t = S
          · subst hts
            exact hx.1
          · exact hx.2 t (mem_erase.2 ⟨hts, ht⟩)
      have hsup : F.sup' hne (fun s => s) = S ∪ U := by
        ext x
        simp only [mem_union, mem_sup']
        constructor
        · rintro ⟨t, ht, hxt⟩
          by_cases hts : t = S
          · subst hts
            exact Or.inl hxt
          · exact Or.inr ⟨t, mem_erase.2 ⟨hts, ht⟩, hxt⟩
        · rintro (hxS | ⟨t, ht, hxt⟩)
          · exact ⟨S, hS, hxS⟩
          · exact ⟨t, mem_of_mem_erase ht, hxt⟩
      have hIU : I ⊆ U := by
        intro x hx
        obtain ⟨W, hW⟩ := hne'
        exact (mem_sup' hne').2 ⟨W, hW, (mem_inf' hne').1 hx W hW⟩
      have hT := isIndepSet_inf_union_slice G F' hne'
        (fun t hs => hmax t (mem_of_mem_erase hs)) S (hmax S hS)
      have hTle : (I ∪ (S ∩ U)).card ≤ G.indepNum :=
        (isIndepSet_subset G (by intro x hx; exact_mod_cast hx)
          (by simpa using hT)).card_le_indepNum
      have hScard : S.card = G.indepNum := (hmax S hS).card_eq
      have hid := card_slice_identity I S U hIU
      have hloss : (I \ S).card ≤ (S \ U).card := by
        have : (I ∪ (S ∩ U)).card ≤ S.card := by simpa [hScard] using hTle
        omega
      have : (S ∩ I).card + (S ∪ U).card ≥ I.card + U.card := by
        have hid' := hid
        have hSI : (S ∩ I).card = (I ∩ S).card := by rw [inter_comm]
        have hSU : (S ∪ U).card = (I ∪ (S ∩ U)).card + (S \ U).card - (I \ S).card := by
          omega
        -- Direct comparison via disjoint decompositions.
        have h1 : (I ∩ S).card + (I \ S).card = I.card := by
          have hinter : I ∩ S ∪ (I \ S) = I := by
            ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
          have hdisj : Disjoint (I ∩ S) (I \ S) := disjoint_sdiff
          rw [← hinter, card_union_of_disjoint hdisj]
        have h2 : (S ∪ U).card = U.card + (S \ U).card := by
          have : U ∪ (S \ U) = S ∪ U := by
            ext x
            simp only [mem_union, mem_sdiff]
            constructor
            · rintro (hU | ⟨hS, hU⟩)
              · exact Or.inr hU
              · exact Or.inl hS
            · rintro (hS | hU)
              · by_cases hxU : x ∈ U
                · exact Or.inl hxU
                · exact Or.inr ⟨hS, hxU⟩
              · exact Or.inl hU
          have hdisj : Disjoint U (S \ U) := by
            intro x hx
            simp [mem_sdiff] at hx
          rw [union_comm, ← this]
          simpa [union_comm] using card_union_of_disjoint (by
            intro x hx
            simp [inf_eq_inter, mem_inter, mem_sdiff] at hx)
        -- Recompute cleanly.
        clear hSU
        rw [hSI]
        have : (I ∩ S).card + (S ∪ U).card = I.card - (I \ S).card + U.card + (S \ U).card := by
          have : (I ∩ S).card = I.card - (I \ S).card := by omega
          omega
        omega
      have : 2 * G.indepNum ≤ (S ∩ I).card + (S ∪ U).card := by
        have := ih'
        omega
      simpa [hinf, hsup] using this
    · have hF' : F' = ∅ := not_nonempty_iff_eq_empty.mp hne'
      have hF : F = {S} := by
        rw [← insert_erase hS]
        simp [F', hF']
      have hScard : S.card = G.indepNum := (hmax S hS).card_eq
      simp [hF, inf'_singleton, sup'_singleton, hScard]

lemma two_mul_indepNum_le_card_add_alphaCore :
    2 * G.indepNum ≤ Fintype.card α + (alphaCore G).card := by
  set Ω := G.maxFamily
  have hΩ := G.maxFamily_nonempty
  have hmax : ∀ s ∈ Ω, G.IsNIndepSet G.indepNum s := fun s hs => (G.mem_maxFamily_iff).1 hs
  have hfam := two_mul_indepNum_le_inf_add_sup G Ω hΩ hmax
  have hcore : (Ω.inf' hΩ (fun s => s)).card = (alphaCore G).card := by
    rw [alphaCore_eq_inf_maxFamily]
  have hsup : (Ω.sup' hΩ (fun s => s)).card ≤ Fintype.card α := card_le_univ _
  calc
    2 * G.indepNum ≤ (Ω.inf' hΩ (fun s => s)).card + (Ω.sup' hΩ (fun s => s)).card := hfam
    _ ≤ (Ω.inf' hΩ (fun s => s)).card + Fintype.card α := Nat.add_le_add_left hsup _
    _ = (alphaCore G).card + Fintype.card α := by rw [hcore]
    _ = Fintype.card α + (alphaCore G).card := Nat.add_comm _ _

/-- Exact frozen proposition of `WrittenOnTheWallII.GraphConjecture101.conjecture101`. -/
theorem conjecture101 (h : G.Connected) :
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
