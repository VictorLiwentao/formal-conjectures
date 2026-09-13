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

Original statement formalization: The Formal Conjectures Authors, 2025.
New independent Lean development and write-up: Wentao Li, 2026.
Mathematics: N. Alon, J. Kahn and P. D. Seymour, Large induced degenerate
subgraphs, Graphs and Combinatorics 3 (1987), 203–211, Theorem 1.3 and
Corollary 1.4, specialized to induced bipartite subgraphs via 2-colorings.
This is not a new mathematical discovery.
AI assistance: Cursor Grok 4.6 Extra High.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Induced
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
Independent Lean proof of
`WrittenOnTheWallII.GraphConjecture20.conjecture20`.

This file does not import the frozen sorry theorem. It uses the existing
`b` / induced-bipartite API from `FormalConjecturesForMathlib` unchanged.
-/

set_option linter.unusedSectionVars false
set_option linter.style.moduleDocstring false
set_option autoImplicit false

noncomputable section

open scoped Classical
open SimpleGraph Finset

namespace WOWII20

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Alon–Kahn–Seymour vertex weight for the forest / 2-colorable bound. -/
def aksWeight (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℝ :=
  min (1 : ℝ) (2 / ((G.degree v : ℝ) + 1))

lemma aksWeight_le_one (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    aksWeight G v ≤ 1 :=
  min_le_left _ _

lemma aksWeight_nonneg (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    0 ≤ aksWeight G v :=
  le_min (by norm_num) (div_nonneg (by norm_num) (by positivity))

lemma aksWeight_eq_two_div (G : SimpleGraph α) [DecidableRel G.Adj] {v : α}
    (h : 1 ≤ G.degree v) : aksWeight G v = 2 / ((G.degree v : ℝ) + 1) := by
  unfold aksWeight
  rw [min_eq_right]
  have : (2 : ℝ) ≤ (G.degree v : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  exact (div_le_one (by positivity)).2 this

lemma min_two_div_anti {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    min (1 : ℝ) (2 / ((d₂ : ℝ) + 1)) ≤ min 1 (2 / ((d₁ : ℝ) + 1)) := by
  refine min_le_min le_rfl ?_
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (by exact_mod_cast Nat.succ_le_succ h)

lemma fin2_add_one_ne (c : Fin 2) : c + 1 ≠ c := by
  rcases Fin.fin_two_eq_zero_or_one c with hc | hc <;> subst hc <;> decide

lemma compl_singleton_toFinset (v : α) :
    ({v}ᶜ : Set α).toFinset = univ.erase v := by
  ext x
  simp [Set.mem_compl_iff]

lemma card_compl_singleton (v : α) :
    Fintype.card (↥({v}ᶜ : Set α)) = Fintype.card α - 1 := by
  rw [Fintype.card_coe, compl_singleton_toFinset, card_erase_of_mem (mem_univ v)]

lemma mem_compl_singleton {v x : α} : x ∈ ({v}ᶜ : Set α) ↔ x ≠ v :=
  Set.mem_compl_iff _ _

lemma neighbor_unique (G : SimpleGraph α) [DecidableRel G.Adj] {v x y : α}
    (hv : G.degree v ≤ 1) (hx : G.Adj v x) (hy : G.Adj v y) : x = y := by
  refine (card_le_one.mp (show #(G.neighborFinset v) ≤ 1 from hv)) ?_ ?_
  · exact (mem_neighborFinset _ _ _).2 hx
  · exact (mem_neighborFinset _ _ _).2 hy

lemma degree_induce_compl_singleton (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (u : ↥({v}ᶜ : Set α)) :
    (G.induce ({v}ᶜ : Set α)).degree u =
      if G.Adj (u : α) v then G.degree (u : α) - 1 else G.degree (u : α) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hmap := map_neighborFinset_induce (G := G) (s := ({v}ᶜ : Set α)) u
  have hcard := congrArg Finset.card hmap
  rw [card_map] at hcard
  rw [hcard, compl_singleton_toFinset]
  have hinter :
      G.neighborFinset (u : α) ∩ univ.erase v = (G.neighborFinset (u : α)).erase v := by
    ext x
    constructor
    · intro hx
      rw [mem_inter, mem_erase] at hx
      exact mem_erase.2 ⟨hx.2.1, hx.1⟩
    · intro hx
      rw [mem_erase] at hx
      exact mem_inter.2 ⟨hx.2, mem_erase.2 ⟨hx.1, mem_univ x⟩⟩
  rw [hinter]
  by_cases hvw : G.Adj (u : α) v
  · have : v ∈ G.neighborFinset (u : α) := (mem_neighborFinset _ _ _).2 hvw
    rw [card_erase_of_mem this, if_pos hvw]
  · have : v ∉ G.neighborFinset (u : α) := by
      simpa [mem_neighborFinset] using hvw
    rw [erase_eq_of_notMem this, if_neg hvw]

lemma aksWeight_induce_ge (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (u : ↥({v}ᶜ : Set α)) :
    aksWeight G (u : α) ≤ aksWeight (G.induce ({v}ᶜ : Set α)) u := by
  unfold aksWeight
  have hdeg : (G.induce ({v}ᶜ : Set α)).degree u ≤ G.degree (u : α) := by
    rw [degree_induce_compl_singleton]
    split_ifs
    · exact Nat.sub_le _ _
    · exact le_rfl
  exact min_two_div_anti hdeg

lemma sum_aksWeight_coe_compl (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) =
      ∑ u ∈ univ.erase v, aksWeight G u := by
  rw [Finset.sum_set_coe (s := ({v}ᶜ : Set α)), compl_singleton_toFinset]

lemma sum_aksWeight_erase_add (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    ∑ u, aksWeight G u =
      aksWeight G v + ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) := by
  rw [sum_aksWeight_coe_compl, ← sum_erase_add (mem_univ v), add_comm]

/-- The `sSup` defining `b` is bounded by `n` and any feasible set is a witness. -/
lemma le_b (G : SimpleGraph α) (s : Finset α)
    (hs : (G.induce (s : Set α)).IsBipartite) : (s.card : ℝ) ≤ b G := by
  simp only [b]
  exact_mod_cast
    (le_csSup ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩ ⟨s, hs, rfl⟩)

lemma exists_coloring_insert_deg_le_one (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (hv : G.degree v ≤ 1) (s : Finset α) (hs : v ∉ s) (c : α → Fin 2)
    (hc : ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w) :
    ∃ c' : α → Fin 2,
      ∀ u ∈ insert v s, ∀ w ∈ insert v s, G.Adj u w → c' u ≠ c' w := by
  let nbrs := G.neighborFinset v ∩ s
  refine ⟨fun x =>
      if x = v then (if h : nbrs.Nonempty then c h.choose + 1 else 0) else c x, ?_⟩
  intro u hu w hw hadj
  rw [mem_insert] at hu hw
  rcases hu with hu | hu <;> rcases hw with hw | hw
  · subst hu; subst hw
    exact (hadj.ne rfl).elim
  · subst hu
    have hne : w ≠ v := fun h => hs (h ▸ hw)
    have hex : nbrs.Nonempty :=
      ⟨w, mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, hw⟩⟩
    simp [hne, hex]
    have hch := hex.choose_spec
    have hadj' : G.Adj v hex.choose :=
      (mem_neighborFinset _ _ _).1 (mem_inter.mp hch).1
    have : hex.choose = w := neighbor_unique G hv hadj' hadj
    rw [this]
    exact fin2_add_one_ne (c w)
  · subst hw
    have hne : u ≠ v := fun h => hs (h ▸ hu)
    have hex : nbrs.Nonempty :=
      ⟨u, mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj.symm, hu⟩⟩
    simp [hne, hex]
    have hch := hex.choose_spec
    have hadj' : G.Adj v hex.choose :=
      (mem_neighborFinset _ _ _).1 (mem_inter.mp hch).1
    have : hex.choose = u := neighbor_unique G hv hadj' hadj.symm
    rw [this]
    exact (fin2_add_one_ne (c u)).symm
  · have hu' : u ≠ v := fun h => hs (h ▸ hu)
    have hw' : w ≠ v := fun h => hs (h ▸ hw)
    simp [hu', hw']
    exact hc u hu w hw hadj

lemma two_div_sub {t : ℕ} (ht : 0 < t) :
    (2 : ℝ) / t - 2 / (t + 1) = 2 / (t * (t + 1) : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  field_simp [ht0]
  ring

lemma aksWeight_gain_neighbor (G : SimpleGraph α) [DecidableRel G.Adj]
    {v : α} (u : ↥({v}ᶜ : Set α)) (hD : 2 ≤ G.degree v)
    (hdeg : 2 ≤ G.degree (u : α)) (hle : G.degree (u : α) ≤ G.degree v)
    (hadj : G.Adj (u : α) v) :
    aksWeight G (u : α) + 2 / ((G.degree v : ℝ) * (G.degree v + 1)) ≤
      aksWeight (G.induce ({v}ᶜ : Set α)) u := by
  have hu1 : 1 ≤ G.degree (u : α) := le_trans (by norm_num : (1 : ℕ) ≤ 2) hdeg
  rw [aksWeight_eq_two_div (v := (u : α)) hu1]
  have hdeg' :
      (G.induce ({v}ᶜ : Set α)).degree u = G.degree (u : α) - 1 := by
    rw [degree_induce_compl_singleton, if_pos hadj]
  have hdeg'1 : 1 ≤ (G.induce ({v}ᶜ : Set α)).degree u := by
    rw [hdeg']
    exact (Nat.le_sub_iff_add_le hu1).2 (by exact hdeg)
  rw [aksWeight_eq_two_div (G := G.induce ({v}ᶜ : Set α)) hdeg'1, hdeg']
  have hcast :
      ((G.degree (u : α) - 1 : ℕ) : ℝ) + 1 = (G.degree (u : α) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hu1
  rw [hcast]
  have ht : 0 < G.degree (u : α) := Nat.succ_le_iff.mp hu1
  have hgain := two_div_sub ht
  have hmono :
      (2 : ℝ) / ((G.degree v : ℝ) * (G.degree v + 1)) ≤
        2 / ((G.degree (u : α) : ℝ) * (G.degree (u : α) + 1)) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    have : (G.degree (u : α) : ℝ) ≤ G.degree v := by exact_mod_cast hle
    nlinarith
  linarith [hgain]

/-- Neighbours of `v` as vertices of `G.induce {v}ᶜ`. -/
def neighborCompl (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    Finset ↥({v}ᶜ : Set α) :=
  univ.filter fun u : ↥({v}ᶜ : Set α) => G.Adj (u : α) v

lemma mem_neighborCompl_iff (G : SimpleGraph α) [DecidableRel G.Adj] (v : α)
    (u : ↥({v}ᶜ : Set α)) : u ∈ neighborCompl G v ↔ G.Adj (u : α) v := by
  simp [neighborCompl]

lemma card_neighborCompl (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    (neighborCompl G v).card = G.degree v := by
  refine (card_bij (fun (u : ↥({v}ᶜ : Set α)) (_ : u ∈ neighborCompl G v) => (u : α))
      ?_ ?_ ?_).trans card_neighborFinset_eq_degree
  · intro u hu
    exact (mem_neighborFinset _ _ _).2 ((mem_neighborCompl_iff G v u).1 hu)
  · intro u hu w hw h
    exact Subtype.ext h
  · intro x hx
    have hadj : G.Adj v x := (mem_neighborFinset _ _ _).1 hx
    have hne : x ≠ v := hadj.ne.symm
    refine ⟨⟨x, mem_compl_singleton.2 hne⟩, ?_, rfl⟩
    exact (mem_neighborCompl_iff _ _ _).2 hadj.symm

lemma aksWeight_induce_eq_of_not_adj (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (u : ↥({v}ᶜ : Set α)) (h : ¬ G.Adj (u : α) v) :
    aksWeight (G.induce ({v}ᶜ : Set α)) u = aksWeight G (u : α) := by
  unfold aksWeight
  rw [degree_induce_compl_singleton, if_neg h]

lemma weight_delete_max_ge (G : SimpleGraph α) [DecidableRel G.Adj] (v : α)
    (hdeg : ∀ u : α, 2 ≤ G.degree u) (hv : G.degree v = G.maxDegree) :
    ∑ u, aksWeight G u ≤
      ∑ u : ↥({v}ᶜ : Set α), aksWeight (G.induce ({v}ᶜ : Set α)) u := by
  set G' : SimpleGraph (↥({v}ᶜ : Set α)) := G.induce ({v}ᶜ : Set α)
  have hD2 : 2 ≤ G.degree v := hdeg v
  have hmax : ∀ u, G.degree u ≤ G.degree v := fun u => hv ▸ degree_le_maxDegree G u
  have hsplit :
      ∑ u : ↥({v}ᶜ : Set α), aksWeight G' u =
        ∑ u ∈ neighborCompl G v, aksWeight G' u +
          ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G' u := by
    exact (sum_add_sum_compl (neighborCompl G v) _).symm
  have hN :
      ∑ u ∈ neighborCompl G v, aksWeight G (u : α) +
          (neighborCompl G v).card • (2 / ((G.degree v : ℝ) * (G.degree v + 1))) ≤
        ∑ u ∈ neighborCompl G v, aksWeight G' u := by
    have hpt : ∀ u ∈ neighborCompl G v,
        aksWeight G (u : α) + 2 / ((G.degree v : ℝ) * (G.degree v + 1)) ≤
          aksWeight G' u := by
      intro u hu
      have hadj : G.Adj (u : α) v := (mem_neighborCompl_iff _ _ _).1 hu
      exact aksWeight_gain_neighbor (G := G) (v := v) u hD2 (hdeg (u : α)) (hmax (u : α)) hadj
    calc
      ∑ u ∈ neighborCompl G v, aksWeight G (u : α) +
          (neighborCompl G v).card • (2 / ((G.degree v : ℝ) * (G.degree v + 1)))
        = ∑ u ∈ neighborCompl G v,
            (aksWeight G (u : α) + 2 / ((G.degree v : ℝ) * (G.degree v + 1))) := by
          simp [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ neighborCompl G v, aksWeight G' u := sum_le_sum hpt
  have hNc :
      ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G' u =
        ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G (u : α) := by
    refine sum_congr rfl fun u hu => ?_
    have : ¬ G.Adj (u : α) v := by
      simpa [mem_compl, mem_neighborCompl_iff] using hu
    exact aksWeight_induce_eq_of_not_adj G v u this
  have hold :
      ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) =
        ∑ u ∈ neighborCompl G v, aksWeight G (u : α) +
          ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G (u : α) :=
    (sum_add_sum_compl (neighborCompl G v) _).symm
  have hcardN : ((neighborCompl G v).card : ℝ) = G.degree v := by
    exact_mod_cast card_neighborCompl G v
  have hwv : aksWeight G v = 2 / ((G.degree v : ℝ) + 1) :=
    aksWeight_eq_two_div (le_trans (by norm_num : (1 : ℕ) ≤ 2) hD2)
  have hgain :
      (neighborCompl G v).card • (2 / ((G.degree v : ℝ) * (G.degree v + 1))) =
        aksWeight G v := by
    rw [nsmul_eq_mul, hcardN, hwv]
    have hDpos : (G.degree v : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_ne_zero fun h => by omega)
    field_simp [hDpos]
    ring
  have hW := sum_aksWeight_erase_add G v
  calc
    ∑ u, aksWeight G u
      = aksWeight G v + ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) := hW
    _ = aksWeight G v +
          (∑ u ∈ neighborCompl G v, aksWeight G (u : α) +
            ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G (u : α)) := by
        rw [hold]
    _ = ∑ u ∈ neighborCompl G v, aksWeight G (u : α) +
          (neighborCompl G v).card • (2 / ((G.degree v : ℝ) * (G.degree v + 1))) +
            ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G (u : α) := by
        rw [← hgain]; abel
    _ ≤ ∑ u ∈ neighborCompl G v, aksWeight G' u +
          ∑ u ∈ (neighborCompl G v)ᶜ, aksWeight G' u := by
        rw [hNc]; linarith [hN]
    _ = ∑ u : ↥({v}ᶜ : Set α), aksWeight G' u :=
        sum_add_sum_compl (neighborCompl G v) (aksWeight G')

lemma image_val_not_mem (v : α) (s' : Finset ↥({v}ᶜ : Set α)) :
    v ∉ s'.image Subtype.val := by
  intro hv
  obtain ⟨u, _, hu⟩ := mem_image.mp hv
  exact (mem_compl_singleton.1 u.property) hu

lemma lift_induce_bipartite (G : SimpleGraph α) (v : α)
    (s' : Finset ↥({v}ᶜ : Set α))
    (hs' : ((G.induce ({v}ᶜ : Set α)).induce (s' : Set ↥({v}ᶜ : Set α))).IsBipartite) :
    (G.induce (s'.image Subtype.val : Set α)).IsBipartite := by
  rw [induce_isBipartite_iff_exists_coloring] at hs' ⊢
  obtain ⟨c', hc'⟩ := hs'
  refine ⟨fun x => if h : x ≠ v then c' ⟨x, mem_compl_singleton.2 h⟩ else 0, ?_⟩
  intro x hx y hy hadj
  obtain ⟨ux, hux, rfl⟩ := mem_image.mp hx
  obtain ⟨uy, huy, rfl⟩ := mem_image.mp hy
  have hxne : (ux : α) ≠ v := mem_compl_singleton.1 ux.property
  have hyne : (uy : α) ≠ v := mem_compl_singleton.1 uy.property
  simp [hxne, hyne]
  have hadj' : (G.induce ({v}ᶜ : Set α)).Adj ux uy := hadj
  exact hc' ux hux uy huy hadj'

lemma antivary_inv_succ (f : α → ℕ) :
    Antivary (fun a : α => (1 : ℝ) / (f a + 1)) (fun a => (f a + 1 : ℝ)) := by
  intro i j
  dsimp
  rcases le_total (f i) (f j) with hij | hji
  · have hg : (f i + 1 : ℝ) ≤ f j + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have hf : (1 : ℝ) / (f j + 1) ≤ 1 / (f i + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hg
    nlinarith
  · have hg : (f j + 1 : ℝ) ≤ f i + 1 := by exact_mod_cast Nat.add_le_add_right hji 1
    have hf : (1 : ℝ) / (f i + 1) ≤ 1 / (f j + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hg
    nlinarith

lemma sum_aksWeight_ge_two_n_div (G : SimpleGraph α) [DecidableRel G.Adj]
    [Nonempty α] (hdeg : ∀ v, 1 ≤ G.degree v) :
    (2 * Fintype.card α : ℝ) /
        (((∑ v, (G.degree v : ℝ)) / (Fintype.card α : ℝ)) + 1) ≤
      ∑ v, aksWeight G v := by
  have hnpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hA := (antivary_inv_succ G.degree).card_mul_sum_le_sum_mul_sum
  have hfg : ∀ v, ((1 : ℝ) / (G.degree v + 1)) * (G.degree v + 1 : ℝ) = 1 := by
    intro v
    exact div_mul_cancel₀ _ (by positivity)
  simp_rw [hfg] at hA
  have hsum1 : ∑ v : α, (1 : ℝ) = (Fintype.card α : ℝ) := by simp
  rw [hsum1] at hA
  have hW : ∑ v, aksWeight G v = 2 * ∑ v, (1 : ℝ) / (G.degree v + 1) := by
    rw [← Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [aksWeight_eq_two_div (hdeg v), div_eq_mul_inv, one_div]
  have hg : ∑ v, (G.degree v + 1 : ℝ) = (∑ v, (G.degree v : ℝ)) + Fintype.card α := by
    simp [sum_add_distrib]
  have hdenpos : 0 < (∑ v, (G.degree v : ℝ)) + Fintype.card α := by positivity
  have hCS : (Fintype.card α : ℝ) * Fintype.card α ≤
      (∑ v, (1 : ℝ) / (G.degree v + 1)) * ∑ v, (G.degree v + 1 : ℝ) := hA
  have : (2 * Fintype.card α : ℝ) /
      (((∑ v, (G.degree v : ℝ)) / (Fintype.card α : ℝ)) + 1) =
        2 * (Fintype.card α : ℝ) ^ 2 / ((∑ v, (G.degree v : ℝ)) + Fintype.card α) := by
    field_simp [hnpos.ne']
    ring
  rw [this, hW, hg]
  refine (div_le_iff₀ hdenpos).2 ?_
  nlinarith

/-- Every finite graph has an induced bipartite set of AKS weight. -/
lemma exists_induced_bipartite_ge_weight :
    ∀ (n : ℕ) {α : Type*} [Fintype α] [DecidableEq α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      Fintype.card α = n →
      ∃ s : Finset α, (G.induce (s : Set α)).IsBipartite ∧
        ∑ v, aksWeight G v ≤ (s.card : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α _ _ G _ hn
    by_cases h0 : n = 0
    · subst h0
      have : Fintype.card α = 0 := hn
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp this
      refine ⟨∅, ?_, by simp⟩
      rw [induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero h0
    haveI : Nonempty α := Fintype.card_pos_iff.mp (hn ▸ hnpos)
    by_cases hlow : ∃ v : α, G.degree v ≤ 1
    · obtain ⟨v, hv⟩ := hlow
      have hcard : Fintype.card (↥({v}ᶜ : Set α)) = n - 1 := by
        rw [card_compl_singleton, hn]
      have hlt : Fintype.card (↥({v}ᶜ : Set α)) < n := by
        rw [hcard]; omega
      obtain ⟨s', hs', hsw⟩ :=
        ih (Fintype.card (↥({v}ᶜ : Set α))) hlt (G.induce ({v}ᶜ : Set α)) rfl
      let s : Finset α := s'.image Subtype.val
      have hs_card : s.card = s'.card := card_image_of_injective _ Subtype.val_injective
      have hvns : v ∉ s := image_val_not_mem v s'
      have hbip_s : (G.induce (s : Set α)).IsBipartite :=
        lift_induce_bipartite G v s' hs'
      rw [induce_isBipartite_iff_exists_coloring] at hbip_s
      obtain ⟨c, hc⟩ := hbip_s
      obtain ⟨c', hc'⟩ := exists_coloring_insert_deg_le_one G v hv s hvns c hc
      refine ⟨insert v s, ?_, ?_⟩
      · rw [induce_isBipartite_iff_exists_coloring]
        exact ⟨c', hc'⟩
      · have hpoint :
            ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) ≤
              ∑ u : ↥({v}ᶜ : Set α), aksWeight (G.induce ({v}ᶜ : Set α)) u :=
          sum_le_sum fun u _ => aksWeight_induce_ge G v u
        have hW := sum_aksWeight_erase_add G v
        have hvle : aksWeight G v ≤ 1 := aksWeight_le_one G v
        have hsc : ((insert v s).card : ℝ) = s'.card + 1 := by
          rw [card_insert_of_notMem hvns, hs_card, Nat.cast_add, Nat.cast_one]
        calc
          ∑ u, aksWeight G u
            = aksWeight G v + ∑ u : ↥({v}ᶜ : Set α), aksWeight G (u : α) := hW
          _ ≤ 1 + ∑ u : ↥({v}ᶜ : Set α), aksWeight (G.induce ({v}ᶜ : Set α)) u := by
              nlinarith
          _ ≤ 1 + (s'.card : ℝ) := by nlinarith
          _ = (insert v s).card := by linarith
    · push_neg at hlow
      have hdeg2 : ∀ u : α, 2 ≤ G.degree u := fun u => Nat.succ_le_succ (hlow u)
      obtain ⟨v, hv⟩ := exists_maximal_degree_vertex G
      have hcard : Fintype.card (↥({v}ᶜ : Set α)) = n - 1 := by
        rw [card_compl_singleton, hn]
      have hlt : Fintype.card (↥({v}ᶜ : Set α)) < n := by
        rw [hcard]; omega
      obtain ⟨s', hs', hsw⟩ :=
        ih (Fintype.card (↥({v}ᶜ : Set α))) hlt (G.induce ({v}ᶜ : Set α)) rfl
      let s : Finset α := s'.image Subtype.val
      refine ⟨s, lift_induce_bipartite G v s' hs', ?_⟩
      have hWle := weight_delete_max_ge G v hdeg2 hv
      have hs_card : (s.card : ℝ) = s'.card := by
        exact_mod_cast card_image_of_injective s' Subtype.val_injective
      nlinarith

lemma exists_induced_bipartite_ge_weight' (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ s : Finset α, (G.induce (s : Set α)).IsBipartite ∧
      ∑ v, aksWeight G v ≤ (s.card : ℝ) :=
  exists_induced_bipartite_ge_weight (Fintype.card α) G rfl

lemma connected_degree_ge_one [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (h : G.Connected) (v : α) : 1 ≤ G.degree v :=
  Nat.succ_le_of_lt (h.preconnected.degree_pos_of_nontrivial v)

lemma connected_avg_ge_one [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (h : G.Connected) :
    (1 : ℝ) ≤ (∑ v, (G.degree v : ℝ)) / (Fintype.card α : ℝ) := by
  have hnpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (Fintype.card α : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
    have : ∑ _v : α, (1 : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
      gcongr
      exact_mod_cast connected_degree_ge_one G h _
    simpa using this
  exact (one_le_div hnpos).2 hsum

/-- The frozen WOWII20 bound. -/
theorem conjecture20 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let deg_avg : ℝ := (∑ v : α, (G.degree v : ℝ)) / (Fintype.card α : ℝ)
    (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤ (b G : ℝ) := by
  intro deg_avg
  have hnpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hdeg1 : ∀ v, 1 ≤ G.degree v := connected_degree_ge_one G h
  have havg : (1 : ℝ) ≤ deg_avg := connected_avg_ge_one G h
  haveI : Nonempty α := inferInstance
  obtain ⟨s, hs, hsw⟩ := exists_induced_bipartite_ge_weight' G
  have hsb := le_b G s hs
  by_cases hlt : deg_avg < 2
  · have hfl : ⌊deg_avg⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast havg
      · exact hlt
    have hE : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
      G.sum_degrees_eq_twice_card_edges
    have havg' : deg_avg = (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card α : ℝ) := by
      simp [deg_avg, hE, Nat.cast_mul, Nat.cast_ofNat]
    have hedges_lt : G.edgeFinset.card < Fintype.card α := by
      have : (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card α : ℝ) < 2 := by
        rwa [← havg']
      have : (2 * (G.edgeFinset.card : ℝ)) < 2 * Fintype.card α :=
        (div_lt_iff₀ hnpos).mp this
      have : (G.edgeFinset.card : ℝ) < (Fintype.card α : ℝ) := by nlinarith
      exact_mod_cast this
    have hedges_ge : Fintype.card α ≤ G.edgeFinset.card + 1 := by
      have := h.card_vert_le_card_edgeSet_add_one
      simpa [Nat.card_eq_fintype_card, edgeFinset_card] using this
    have htree : G.IsTree := by
      rw [isTree_iff_connected_and_card]
      refine ⟨h, ?_⟩
      simp [Nat.card_eq_fintype_card, edgeFinset_card]
      omega
    have hbip : G.IsBipartite := htree.isBipartite
    have huniv : (G.induce (univ : Set α)).IsBipartite := by
      rw [induce_isBipartite_iff_exists_coloring]
      obtain ⟨c⟩ := hbip
            exact ⟨fun x => c x, fun u _ w _ hadj => Coloring.valid c hadj⟩
    have hbn : (Fintype.card α : ℝ) ≤ b G := by
      simpa [card_univ] using le_b G univ huniv
    simp [hfl]
    exact hbn
  · have hge : (2 : ℝ) ≤ deg_avg := le_of_not_gt hlt
    have hk2 : (2 : ℤ) ≤ ⌊deg_avg⌋ := (Int.le_floor).2 (by exact_mod_cast hge)
    have hk2r : (2 : ℝ) ≤ (⌊deg_avg⌋ : ℝ) := by exact_mod_cast hk2
    have hkpos : (0 : ℝ) < (⌊deg_avg⌋ : ℝ) := lt_of_lt_of_le (by norm_num) hk2r
    have hfl_lt : deg_avg < (⌊deg_avg⌋ : ℝ) + 1 := Int.lt_floor_add_one deg_avg
    have hden : deg_avg + 1 ≤ 2 * (⌊deg_avg⌋ : ℝ) := by linarith
    have hCS := sum_aksWeight_ge_two_n_div (G := G) hdeg1
    have hfrac :
        (Fintype.card α : ℝ) / (⌊deg_avg⌋ : ℝ) ≤
          (2 * Fintype.card α : ℝ) / (deg_avg + 1) := by
      rw [div_le_div_iff₀ hkpos (by positivity)]
      nlinarith
    have : (2 * Fintype.card α : ℝ) / (deg_avg + 1) ≤ ∑ v, aksWeight G v := by
      simpa [deg_avg] using hCS
    linarith [hfrac, this, hsw, hsb]

end WOWII20

#print axioms WOWII20.conjecture20
#check WOWII20.conjecture20
