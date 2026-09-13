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

Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.
-/

import FormalConjectures.OEIS.«108081»
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Structural lemmas for OEIS A108081

This file develops lemmas toward
`OeisA108081.count_words_in_x_is_a_shifted`.
It does not prove that identity.
-/

set_option autoImplicit false

namespace OeisA108081

open List

-- `l` and `r`

lemma length_l (w : Word) : (l w).length = w.length := by
  simp [l]

lemma length_r (w : Word) : (r w).length = w.length := by
  simp [r]

lemma getElem_l {u : Word} {i : ℕ} (hi : i < (l u).length) :
    (l u)[i] =
      u[u.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt (by simpa [length_l] using hi)) - 1 := by
  simp [l]

lemma getElem_r {v : Word} {i : ℕ} (hi : i < (r v).length) :
    (r v)[i] =
      v[v.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt (by simpa [length_r] using hi)) + 1 := by
  simp [r]

lemma take_r (v : Word) (j : ℕ) :
    (r v).take j = r (v.drop (v.length - j)) := by
  simp [r, take_reverse]

lemma drop_r (v : Word) (j : ℕ) :
    (r v).drop j = r (v.take (v.length - j)) := by
  simp [r, drop_reverse]

lemma l_r (w : Word) : l (r w) = w := by
  simp [l, r]
  change w.map (fun x => x + 1 - 1) = w
  simp

lemma r_l (w : Word) : r (l w) = w := by
  simp [l, r]
  change w.map (fun x => x - 1 + 1) = w
  simp

lemma l_injective : Function.Injective l := by
  intro a b h
  simpa [r_l] using congrArg r h

lemma r_injective : Function.Injective r := by
  intro a b h
  simpa [l_r] using congrArg l h

lemma l_append (u v : Word) : l (u ++ v) = l v ++ l u := by
  simp [l, reverse_append]

lemma r_append (u v : Word) : r (u ++ v) = r v ++ r u := by
  simp [r, reverse_append]

lemma l_concat_one (u : Word) : l (u ++ [1]) = 0 :: l u := by
  simp [l]

lemma r_concat_neg_one (v : Word) : r ([-1] ++ v) = r v ++ [0] := by
  simp [r, reverse_cons]

lemma r_zero : r [0] = [1] := by
  simp [r]

lemma l_zero : l [0] = [-1] := by
  simp [l]

lemma l_ne_nil {w : Word} (h : w ≠ []) : l w ≠ [] := by
  simp [l, h]

lemma r_ne_nil {w : Word} (h : w ≠ []) : r w ≠ [] := by
  simp [r, h]

lemma head_l {w : Word} (h : w ≠ []) :
    (l w).head (l_ne_nil h) = w.getLast h - 1 := by
  simp [l, head_reverse]

lemma getLast_r {w : Word} (h : w ≠ []) :
    (r w).getLast (r_ne_nil h) = w.head h + 1 := by
  simp [r, getLast_eq_head_reverse]

-- Nonempty words and endpoints

lemma XWord.ne_nil {w : Word} (hw : XWord w) : w ≠ [] :=
  match hw with
  | .base => by simp
  | .step_left hu hv => append_ne_nil_of_right_ne_nil _ (XWord.ne_nil hv)
  | .step_right hu hv => append_ne_nil_of_left_ne_nil (XWord.ne_nil hu) _

lemma XWord.length_pos {w : Word} (hw : XWord w) : 0 < w.length :=
  length_pos_iff.mpr hw.ne_nil

lemma XWord.length_ge_one {w : Word} (hw : XWord w) : 1 ≤ w.length :=
  Nat.succ_le_of_lt hw.length_pos

lemma mem_endpointSet {x : ℤ} :
    x ∈ ({-1, 0} : Set ℤ) ↔ x = -1 ∨ x = 0 := by
  simp

lemma mem_endpointSet' {x : ℤ} :
    x ∈ ({0, 1} : Set ℤ) ↔ x = 0 ∨ x = 1 := by
  simp

lemma XWord.head_last_mem {w : Word} (hw : XWord w) :
    w.head hw.ne_nil ∈ ({-1, 0} : Set ℤ) ∧
      w.getLast hw.ne_nil ∈ ({0, 1} : Set ℤ) :=
  match w, hw with
  | _, .base => by simp
  | _, @XWord.step_left u v hu hv => by
    have hu_ne := hu.ne_nil
    have hv_ne := hv.ne_nil
    constructor
    · have : (l u ++ v).head (XWord.ne_nil (XWord.step_left hu hv)) =
          (l u).head (l_ne_nil hu_ne) :=
        head_append_of_ne_nil (l_ne_nil hu_ne)
      rw [this, head_l hu_ne]
      have hlast : u.getLast hu_ne = 0 ∨ u.getLast hu_ne = 1 :=
        mem_endpointSet'.mp (XWord.head_last_mem hu).2
      rcases hlast with h | h <;> simp [h]
    · have : (l u ++ v).getLast (XWord.ne_nil (XWord.step_left hu hv)) =
          v.getLast hv_ne :=
        getLast_append_of_right_ne_nil _ _ hv_ne
      rw [this]
      exact (XWord.head_last_mem hv).2
  | _, @XWord.step_right u v hu hv => by
    have hu_ne := hu.ne_nil
    have hv_ne := hv.ne_nil
    constructor
    · have : (u ++ r v).head (XWord.ne_nil (XWord.step_right hu hv)) =
          u.head hu_ne :=
        head_append_of_ne_nil hu_ne
      rw [this]
      exact (XWord.head_last_mem hu).1
    · have : (u ++ r v).getLast (XWord.ne_nil (XWord.step_right hu hv)) =
          (r v).getLast (r_ne_nil hv_ne) :=
        getLast_append_of_right_ne_nil _ _ (r_ne_nil hv_ne)
      rw [this, getLast_r hv_ne]
      have hfirst : v.head hv_ne = -1 ∨ v.head hv_ne = 0 :=
        mem_endpointSet.mp (XWord.head_last_mem hv).1
      rcases hfirst with h | h <;> simp [h]

lemma XWord.head_mem {w : Word} (hw : XWord w) :
    w.head hw.ne_nil ∈ ({-1, 0} : Set ℤ) :=
  (XWord.head_last_mem hw).1

lemma XWord.head_eq_neg_one_or_zero {w : Word} (hw : XWord w) :
    w.head hw.ne_nil = -1 ∨ w.head hw.ne_nil = 0 :=
  mem_endpointSet.mp hw.head_mem

lemma XWord.getLast_mem {w : Word} (hw : XWord w) :
    w.getLast hw.ne_nil ∈ ({0, 1} : Set ℤ) :=
  (XWord.head_last_mem hw).2

lemma XWord.zero_mem {w : Word} (hw : XWord w) : (0 : ℤ) ∈ w :=
  match hw with
  | .base => by simp
  | .step_left hu hv => mem_append.mpr (Or.inr (XWord.zero_mem hv))
  | .step_right hu hv => mem_append.mpr (Or.inl (XWord.zero_mem hu))

lemma mem_l_iff {u : Word} {y : ℤ} : y ∈ l u ↔ y + 1 ∈ u := by
  simp [l, sub_eq_iff_eq_add]

lemma mem_r_iff {v : Word} {y : ℤ} : y ∈ r v ↔ y - 1 ∈ v := by
  simp [r, mem_map, mem_reverse]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa
  · intro h
    exact ⟨y - 1, h, by omega⟩

lemma XWord.neg_one_mem_l {u : Word} (hu : XWord u) : (-1 : ℤ) ∈ l u :=
  mem_l_iff.mpr (by simpa using hu.zero_mem)

lemma XWord.one_mem_r {v : Word} (hv : XWord v) : (1 : ℤ) ∈ r v :=
  mem_r_iff.mpr (by simpa using hv.zero_mem)

/-- The letters of a Xia word form an integer interval. -/
lemma XWord.convex {w : Word} (hw : XWord w) {x y z : ℤ}
    (hx : x ∈ w) (hz : z ∈ w) (hxy : x ≤ y) (hyz : y ≤ z) : y ∈ w :=
  match w, hw with
  | _, .base => by
    simp only [mem_cons, not_mem_nil, or_false] at hx hz
    subst hx
    subst hz
    have : y = 0 := le_antisymm hyz hxy
    simp [this]
  | _, @XWord.step_left u v hu hv => by
    have h0v := hv.zero_mem
    have hm1 := hu.neg_one_mem_l
    have h0w : (0 : ℤ) ∈ l u ++ v := mem_append.mpr (Or.inr h0v)
    by_cases h0y : y = 0
    · simpa [h0y] using h0w
    have hx' := mem_append.mp hx
    have hz' := mem_append.mp hz
    have hyne : y ≠ 0 := h0y
    rcases hx' with hxI | hxJ
    · rcases hz' with hzI | hzJ
      · exact mem_append.mpr (Or.inl (mem_l_iff.mpr
          (hu.convex (mem_l_iff.mp hxI) (mem_l_iff.mp hzI) (by linarith) (by linarith))))
      · rcases le_total y 0 with hy0 | hypos
        · have hyle : y ≤ -1 := by omega
          exact mem_append.mpr (Or.inl (mem_l_iff.mpr
            (hu.convex (mem_l_iff.mp hxI) (mem_l_iff.mp hm1)
              (by linarith) (by linarith))))
        · exact mem_append.mpr (Or.inr
            (hv.convex h0v hzJ (by linarith) hyz))
    · rcases hz' with hzI | hzJ
      · rcases le_total y 0 with hy0 | hypos
        · exact mem_append.mpr (Or.inr (hv.convex hxJ h0v hxy (by omega)))
        · exact mem_append.mpr (Or.inl (mem_l_iff.mpr
            (hu.convex (mem_l_iff.mp hm1) (mem_l_iff.mp hzI)
              (by linarith) (by linarith))))
      · exact mem_append.mpr (Or.inr (hv.convex hxJ hzJ hxy hyz))
  | _, @XWord.step_right u v hu hv => by
    have h0u := hu.zero_mem
    have h1 := hv.one_mem_r
    have h0w : (0 : ℤ) ∈ u ++ r v := mem_append.mpr (Or.inl h0u)
    by_cases h0y : y = 0
    · simpa [h0y] using h0w
    have hx' := mem_append.mp hx
    have hz' := mem_append.mp hz
    rcases hx' with hxI | hxJ
    · rcases hz' with hzI | hzJ
      · exact mem_append.mpr (Or.inl (hu.convex hxI hzI hxy hyz))
      · rcases le_total y 0 with hy0 | hypos
        · exact mem_append.mpr (Or.inl (hu.convex hxI h0u hxy (by omega)))
        · have hy1 : 1 ≤ y := by omega
          exact mem_append.mpr (Or.inr (mem_r_iff.mpr
            (hv.convex (mem_r_iff.mp h1) (mem_r_iff.mp hzJ)
              (by linarith) (by linarith))))
    · rcases hz' with hzI | hzJ
      · rcases le_total y 0 with hy0 | hypos
        · exact mem_append.mpr (Or.inr (mem_r_iff.mpr
            (hv.convex (mem_r_iff.mp hxJ) (mem_r_iff.mp h1)
              (by linarith) (by linarith))))
        · have hy1 : 1 ≤ y := by omega
          exact mem_append.mpr (Or.inl (hu.convex h0u hzI (by linarith) hyz))
      · exact mem_append.mpr (Or.inr (mem_r_iff.mpr
          (hv.convex (mem_r_iff.mp hxJ) (mem_r_iff.mp hzJ)
            (by linarith) (by linarith))))

lemma XWord.neg_one_mem_of_neg {w : Word} (hw : XWord w) {x : ℤ}
    (hx : x ∈ w) (hneg : x < 0) : (-1 : ℤ) ∈ w :=
  hw.convex hx hw.zero_mem (by omega) (by omega)

lemma XWord.one_mem_of_pos {w : Word} (hw : XWord w) {x : ℤ}
    (hx : x ∈ w) (hpos : 0 < x) : (1 : ℤ) ∈ w :=
  hw.convex hw.zero_mem hx (by omega) (by omega)

lemma XWord.nonneg_of_not_mem_neg_one {w : Word} (hw : XWord w)
    (h : (-1 : ℤ) ∉ w) {x : ℤ} (hx : x ∈ w) : 0 ≤ x := by
  by_contra hx'
  exact h (hw.neg_one_mem_of_neg hx (by omega))

lemma XWord.nonpos_of_not_mem_one {w : Word} (hw : XWord w)
    (h : (1 : ℤ) ∉ w) {x : ℤ} (hx : x ∈ w) : x ≤ 0 := by
  by_contra hx'
  exact h (hw.one_mem_of_pos hx (by omega))

-- Entry bounds and finiteness of `xN`

lemma XWord.mem_bounds {w : Word} (hw : XWord w) {x : ℤ} (hx : x ∈ w) :
    x ∈ Set.Icc ((1 : ℤ) - w.length) (w.length - 1) :=
  match w, hw with
  | _, .base => by
    simp at hx
    simp [hx]
  | _, @XWord.step_left u v hu hv => by
    simp only [length_append, length_l, Set.mem_Icc]
    rcases mem_append.mp hx with hx | hx
    · have hx' : x ∈ u.reverse.map (fun t => t - 1) := by
        simpa [l] using hx
      rcases mem_map.mp hx' with ⟨y, hy, rfl⟩
      have hyu : y ∈ u := mem_reverse.mp hy
      have hyIcc : (1 : ℤ) - u.length ≤ y ∧ y ≤ (u.length : ℤ) - 1 := by
        simpa [Set.mem_Icc] using XWord.mem_bounds hu hyu
      have hvpos : (1 : ℤ) ≤ v.length := by exact_mod_cast hv.length_ge_one
      have hcast : ((u.length + v.length : ℕ) : ℤ) = u.length + v.length := Nat.cast_add _ _
      constructor
      · linarith [hyIcc.1, hvpos, hcast]
      · linarith [hyIcc.2, hvpos, hcast]
    · have hyIcc : (1 : ℤ) - v.length ≤ x ∧ x ≤ (v.length : ℤ) - 1 := by
        simpa [Set.mem_Icc] using XWord.mem_bounds hv hx
      have hupos : (1 : ℤ) ≤ u.length := by exact_mod_cast hu.length_ge_one
      have hcast : ((u.length + v.length : ℕ) : ℤ) = u.length + v.length := Nat.cast_add _ _
      constructor
      · linarith [hyIcc.1, hupos, hcast]
      · linarith [hyIcc.2, hupos, hcast]
  | _, @XWord.step_right u v hu hv => by
    simp only [length_append, length_r, Set.mem_Icc]
    rcases mem_append.mp hx with hx | hx
    · have hyIcc : (1 : ℤ) - u.length ≤ x ∧ x ≤ (u.length : ℤ) - 1 := by
        simpa [Set.mem_Icc] using XWord.mem_bounds hu hx
      have hvpos : (1 : ℤ) ≤ v.length := by exact_mod_cast hv.length_ge_one
      have hcast : ((u.length + v.length : ℕ) : ℤ) = u.length + v.length := Nat.cast_add _ _
      constructor
      · linarith [hyIcc.1, hvpos, hcast]
      · linarith [hyIcc.2, hvpos, hcast]
    · have hx' : x ∈ v.reverse.map (fun t => t + 1) := by
        simpa [r] using hx
      rcases mem_map.mp hx' with ⟨y, hy, rfl⟩
      have hyv : y ∈ v := mem_reverse.mp hy
      have hyIcc : (1 : ℤ) - v.length ≤ y ∧ y ≤ (v.length : ℤ) - 1 := by
        simpa [Set.mem_Icc] using XWord.mem_bounds hv hyv
      have hupos : (1 : ℤ) ≤ u.length := by exact_mod_cast hu.length_ge_one
      have hcast : ((u.length + v.length : ℕ) : ℤ) = u.length + v.length := Nat.cast_add _ _
      constructor
      · linarith [hyIcc.1, hupos, hcast]
      · linarith [hyIcc.2, hupos, hcast]

lemma xN_subset_bounded (n : ℕ) :
    xN n ⊆ {w : Word | w.length = n ∧ ∀ x ∈ w, x ∈ Set.Icc ((1 : ℤ) - n) (n - 1)} := by
  intro w hw
  refine ⟨hw.2, ?_⟩
  intro x hx
  have := XWord.mem_bounds hw.1 hx
  simpa [hw.2] using this

open scoped Classical

lemma xN_finite (n : ℕ) : (xN n).Finite := by
  let S : Set ℤ := Set.Icc ((1 : ℤ) - n) ((n : ℤ) - 1)
  let α := ↥S
  have : Finite α := inferInstance
  have : Finite (List.Vector α n) := inferInstance
  let f : List.Vector α n → Word := fun v => v.toList.map Subtype.val
  have hsub : xN n ⊆ Set.range f := by
    intro w hw
    have hlen := hw.2
    have hmem : ∀ x ∈ w, x ∈ S := fun x hx =>
      (xN_subset_bounded n hw).2 x hx
    let packed :=
      w.pmap (fun x (hx : x ∈ S) => (⟨x, hx⟩ : α)) fun x hx => hmem x hx
    have hp : packed.length = n := by simp [packed, hlen]
    refine ⟨⟨packed, hp⟩, ?_⟩
    change packed.map Subtype.val = w
    simp [packed, map_pmap, pmap_eq_map]
  exact (Set.finite_range f).subset hsub

-- Duality `rho`

/-- Reverse and negate. This swaps the left and right constructors. -/
def rho (w : Word) : Word :=
  w.reverse.map (fun x => -x)

lemma rho_rho (w : Word) : rho (rho w) = w := by
  simp [rho]

lemma length_rho (w : Word) : (rho w).length = w.length := by
  simp [rho]

lemma rho_ne_nil {w : Word} (h : w ≠ []) : rho w ≠ [] := by
  simp [rho, h]

lemma rho_append (u v : Word) : rho (u ++ v) = rho v ++ rho u := by
  simp [rho, reverse_append]

lemma rho_l (w : Word) : rho (l w) = r (rho w) := by
  simp [rho, l, r]
  intro a _
  ring

lemma rho_r (w : Word) : rho (r w) = l (rho w) := by
  simp [rho, l, r]
  intro a _
  ring

lemma rho_head {w : Word} (h : w ≠ []) :
    (rho w).head (rho_ne_nil h) = - w.getLast h := by
  simp [rho, head_reverse]

lemma rho_getLast {w : Word} (h : w ≠ []) :
    (rho w).getLast (rho_ne_nil h) = - w.head h := by
  simp [rho, getLast_eq_head_reverse]

lemma XWord.rho_mem {w : Word} (hw : XWord w) : XWord (rho w) :=
  match w, hw with
  | _, .base => by
    have h0 : OeisA108081.rho [0] = [0] := by
      simp [OeisA108081.rho]
    simpa [h0] using XWord.base
  | _, @XWord.step_left u v hu hv => by
    rw [rho_append, rho_l]
    exact XWord.step_right (XWord.rho_mem hv) (XWord.rho_mem hu)
  | _, @XWord.step_right u v hu hv => by
    rw [rho_append, rho_r]
    exact XWord.step_left (XWord.rho_mem hv) (XWord.rho_mem hu)

-- Parses

def IsLeftParse (w u v : Word) : Prop :=
  XWord u ∧ XWord v ∧ w = l u ++ v

def IsRightParse (w u v : Word) : Prop :=
  XWord u ∧ XWord v ∧ w = u ++ r v

lemma eq_of_left_parse_eq {u u' v v' : Word} (h : l u ++ v = l u' ++ v')
    (hlen : u.length = u'.length) : u = u' ∧ v = v' := by
  have hlen' : (l u).length = (l u').length := by simp [l, hlen]
  have hsplit := append_inj h hlen'
  exact ⟨l_injective hsplit.1, hsplit.2⟩

lemma eq_of_right_parse_eq {u u' v v' : Word} (h : u ++ r v = u' ++ r v')
    (hlen : u.length = u'.length) : u = u' ∧ v = v' := by
  have hsplit := append_inj h hlen
  exact ⟨hsplit.1, r_injective hsplit.2⟩

lemma IsRightParse.length_add {w u v : Word} (h : IsRightParse w u v) :
    u.length + v.length = w.length := by
  rcases h with ⟨_, _, hw⟩
  simp [hw, r]

lemma IsRightParse.take {w u v : Word} (h : IsRightParse w u v) :
    w.take u.length = u := by
  rcases h with ⟨_, _, hw⟩
  simp [hw]

lemma IsRightParse.drop {w u v : Word} (h : IsRightParse w u v) :
    w.drop u.length = r v := by
  rcases h with ⟨_, _, hw⟩
  simp [hw]

lemma IsRightParse.pos_left {w u v : Word} (h : IsRightParse w u v) :
    0 < u.length :=
  (h.1).length_pos

lemma IsRightParse.pos_right {w u v : Word} (h : IsRightParse w u v) :
    0 < v.length :=
  (h.2.1).length_pos

lemma IsRightParse.left_lt_length {w u v : Word} (h : IsRightParse w u v) :
    u.length < w.length := by
  have := h.length_add
  have := h.pos_right
  omega

lemma isRightParse_take_drop {w : Word} {k : ℕ} (_hk0 : 0 < k)
    (_hkl : k < w.length) :
    IsRightParse w (w.take k) (l (w.drop k)) ↔
      XWord (w.take k) ∧ XWord (l (w.drop k)) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro ⟨hu, hv⟩
    refine ⟨hu, hv, ?_⟩
    simp [r_l, take_append_drop]

lemma exists_shortest_right_parse {w : Word} (h : ∃ u v, IsRightParse w u v) :
    ∃ u v, IsRightParse w u v ∧
      ∀ u' v', IsRightParse w u' v' → v.length ≤ v'.length := by
  classical
  obtain ⟨u0, v0, hp0⟩ := h
  let S : Finset ℕ :=
    (Finset.range w.length).filter (fun k =>
      0 < k ∧ XWord (w.take k) ∧ XWord (l (w.drop k)))
  have huS : u0.length ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp0.left_lt_length, ?_⟩
    refine ⟨hp0.pos_left, ?_, ?_⟩
    · simpa [hp0.take] using hp0.1
    · have hdrop := hp0.drop
      simpa [hdrop, l_r] using hp0.2.1
  have hSne : S.Nonempty := ⟨u0.length, huS⟩
  let k := S.max' hSne
  have hkmem := S.max'_mem hSne
  have hk := (Finset.mem_filter.mp hkmem).2
  have hklt : k < w.length := Finset.mem_range.mp (Finset.mem_filter.mp hkmem).1
  refine ⟨w.take k, l (w.drop k), (isRightParse_take_drop hk.1 hklt).mpr ⟨hk.2.1, hk.2.2⟩, ?_⟩
  intro u' v' hp'
  have huS' : u'.length ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp'.left_lt_length, ?_⟩
    refine ⟨hp'.pos_left, ?_, ?_⟩
    · simpa [hp'.take] using hp'.1
    · have hdrop := hp'.drop
      simpa [hdrop, l_r] using hp'.2.1
  have hle : u'.length ≤ k := Finset.le_max' S u'.length huS'
  have hsum := hp'.length_add
  have hk_le : k ≤ w.length := hklt.le
  have hu_lt := hp'.left_lt_length
  have hvlen : (l (w.drop k)).length = w.length - k := by
    simp [length_l, length_drop]
  omega

lemma shortest_right_parse_unique {w u v u' v' : Word}
    (h : IsRightParse w u v) (h' : IsRightParse w u' v')
    (hmin : ∀ u₂ v₂, IsRightParse w u₂ v₂ → v.length ≤ v₂.length)
    (hmin' : ∀ u₂ v₂, IsRightParse w u₂ v₂ → v'.length ≤ v₂.length) :
    u = u' ∧ v = v' := by
  have hv : v.length = v'.length :=
    Nat.le_antisymm (hmin u' v' h') (hmin' u v h)
  have hsum := h.length_add
  have hsum' := h'.length_add
  have hlen : u.length = u'.length := by omega
  exact eq_of_right_parse_eq (h.2.2.symm.trans h'.2.2) hlen

lemma XWord.count_zero_pos {w : Word} (hw : XWord w) : 0 < w.count 0 :=
  count_pos_iff.mpr hw.zero_mem

lemma XWord.not_isAppend_of_count_zero_eq_one {u v w : Word}
    (hu : XWord u) (hv : XWord v) (hw : w = u ++ v)
    (h1 : w.count 0 = 1) : False := by
  have hsum : w.count 0 = u.count 0 + v.count 0 := by
    simp [hw, count_append]
  have := hu.count_zero_pos
  have := hv.count_zero_pos
  omega

/-- Xia words of length `k` with a unique `0`. Experimentally these are
the Catalan-many first peels of `YWord`s. -/
def PWord (w : Word) : Prop :=
  XWord w ∧ w.count 0 = 1

lemma PWord.not_isAppend {u v w : Word} (hw : PWord w) (hu : XWord u)
    (hv : XWord v) (h : w = u ++ v) : False :=
  XWord.not_isAppend_of_count_zero_eq_one hu hv h hw.2

lemma XWord.getLast_eq_zero_or_one {w : Word} (hw : XWord w) :
    w.getLast hw.ne_nil = 0 ∨ w.getLast hw.ne_nil = 1 :=
  mem_endpointSet'.mp hw.getLast_mem

lemma not_xWord_of_getLast_ge_two {w : Word} (h : w ≠ [])
    (ht : 2 ≤ w.getLast h) : ¬ XWord w := by
  intro hw
  have hlast := hw.getLast_eq_zero_or_one
  have : w.getLast hw.ne_nil = w.getLast h := rfl
  omega

lemma getLast_cons_zero_r {s : Word} (hs : s ≠ []) :
    ([0] ++ r s).getLast (append_ne_nil_of_right_ne_nil _ (r_ne_nil hs)) =
      s.head hs + 1 := by
  have h := getLast_append_of_right_ne_nil (l₁ := ([0] : Word)) (l₂ := r s)
    (r_ne_nil hs)
  rw [h, getLast_r hs]

lemma not_xWord_cons_zero_r_of_one_le_head {s : Word} (hs : s ≠ [])
    (hpos : 1 ≤ s.head hs) : ¬ XWord ([0] ++ r s) := by
  intro hw
  have hne : [0] ++ r s ≠ [] := append_ne_nil_of_right_ne_nil _ (r_ne_nil hs)
  have hlast := getLast_cons_zero_r hs
  have hge : 2 ≤ ([0] ++ r s).getLast hne := by
    have : ([0] ++ r s).getLast hne = s.head hs + 1 := hlast
    omega
  exact not_xWord_of_getLast_ge_two hne hge hw

lemma not_xWord_append_r_of_one_le_head {u s : Word} (hs : s ≠ [])
    (hpos : 1 ≤ s.head hs) : ¬ XWord (u ++ r s) := by
  intro hw
  have hne : u ++ r s ≠ [] := append_ne_nil_of_right_ne_nil u (r_ne_nil hs)
  have hlast : (u ++ r s).getLast hne = s.head hs + 1 := by
    rw [getLast_append_of_right_ne_nil (l₁ := u) (l₂ := r s) (r_ne_nil hs),
      getLast_r hs]
  have hge : 2 ≤ (u ++ r s).getLast hne := by omega
  exact not_xWord_of_getLast_ge_two hne hge hw

lemma PWord.base : PWord [0] := by
  refine ⟨XWord.base, ?_⟩
  decide

lemma PWord.neg_one_zero : PWord [-1, 0] := by
  refine ⟨XWord.step_left XWord.base XWord.base, ?_⟩
  decide

lemma PWord.zero_one : PWord [0, 1] := by
  refine ⟨XWord.step_right XWord.base XWord.base, ?_⟩
  decide

lemma count_zero_r (v : Word) : (r v).count 0 = v.count (-1) := by
  simp [r, count_eq_countP, countP_map]
  congr 1
  ext x
  simp [eq_neg_iff_add_eq_zero]

lemma count_zero_l (u : Word) : (l u).count 0 = u.count 1 := by
  simp [l, count_eq_countP, countP_map]
  congr 1
  ext x
  simp [sub_eq_zero]

lemma PWord.of_step_left {u v : Word} (_hu : XWord u) (hv : XWord v)
    (h : PWord (l u ++ v)) : PWord v ∧ u.count 1 = 0 := by
  have hsum : (l u ++ v).count 0 = u.count 1 + v.count 0 := by
    simp [count_append, count_zero_l]
  have hv0 := hv.count_zero_pos
  have h1 : u.count 1 + v.count 0 = 1 := hsum.symm.trans h.2
  have hones : u.count 1 = 0 := by omega
  have hv1 : v.count 0 = 1 := by omega
  exact ⟨⟨hv, hv1⟩, hones⟩

lemma PWord.of_step_right {u v : Word} (hu : XWord u) (_hv : XWord v)
    (h : PWord (u ++ r v)) : PWord u ∧ v.count (-1) = 0 := by
  have hsum : (u ++ r v).count 0 = u.count 0 + v.count (-1) := by
    simp [count_append, count_zero_r]
  have hu0 := hu.count_zero_pos
  have h1 : u.count 0 + v.count (-1) = 1 := hsum.symm.trans h.2
  have hneg : v.count (-1) = 0 := by omega
  have hu1 : u.count 0 = 1 := by omega
  exact ⟨⟨hu, hu1⟩, hneg⟩

lemma PWord.step_right_factor_nonneg {u v : Word} (hu : XWord u) (hv : XWord v)
    (h : PWord (u ++ r v)) {x : ℤ} (hx : x ∈ v) : 0 ≤ x := by
  have hneg := (PWord.of_step_right hu hv h).2
  have hmem : (-1 : ℤ) ∉ v := by
    simpa [count_eq_zero] using hneg
  exact hv.nonneg_of_not_mem_neg_one hmem hx

lemma PWord.step_left_factor_nonpos {u v : Word} (hu : XWord u) (hv : XWord v)
    (h : PWord (l u ++ v)) {x : ℤ} (hx : x ∈ u) : x ≤ 0 := by
  have hones := (PWord.of_step_left hu hv h).2
  have hmem : (1 : ℤ) ∉ u := by
    simpa [count_eq_zero] using hones
  exact hu.nonpos_of_not_mem_one hmem hx

lemma PWord.idxOf_lt_length {w : Word} (hw : PWord w) :
    w.idxOf 0 < w.length :=
  idxOf_lt_length_of_mem hw.1.zero_mem

lemma PWord.getElem_idxOf_zero {w : Word} (hw : PWord w) :
    w[w.idxOf 0]'(hw.idxOf_lt_length) = 0 :=
  getElem_idxOf _

/-- Letters of a one-zero Xia word are strictly negative before the unique `0`
and strictly positive after it. -/
lemma XWord.pword_sign {w : Word} (hw : XWord w) (hc : w.count 0 = 1)
    (i : ℕ) (hi : i < w.length) :
    (i < w.idxOf 0 → w[i] < 0) ∧ (w.idxOf 0 < i → 0 < w[i]) :=
  match w, hw with
  | _, .base => by
    simp at hi
    constructor
    · intro hlt
      simp [idxOf_cons_self] at hlt
    · intro hgt
      simp [idxOf_cons_self] at hgt
      omega
  | _, @XWord.step_left u v hu hv => by
    have hp : PWord (l u ++ v) := ⟨XWord.step_left hu hv, hc⟩
    have hvP := (PWord.of_step_left hu hv hp).1
    have hones := (PWord.of_step_left hu hv hp).2
    have h1u : (1 : ℤ) ∉ u := by simpa [count_eq_zero] using hones
    have h0lu : (0 : ℤ) ∉ l u := fun hmem => h1u (mem_l_iff.mp hmem)
    have hidx : (l u ++ v).idxOf 0 = (l u).length + v.idxOf 0 :=
      idxOf_append_of_notMem h0lu
    have ih (j : ℕ) (hj : j < v.length) := XWord.pword_sign hv hvP.2 j hj
    by_cases hleft : i < (l u).length
    · have hget : (l u ++ v)[i] = (l u)[i] := getElem_append_left hleft
      have hx : u[u.length - 1 - i]'(Nat.sub_one_sub_lt_of_lt
          (by simpa [length_l] using hleft)) ∈ u := getElem_mem _
      have hle := PWord.step_left_factor_nonpos hu hv hp hx
      rw [hget, getElem_l hleft]
      constructor
      · intro _hlt
        omega
      · intro hgt
        have : i < (l u ++ v).idxOf 0 := by
          simp [hidx]
          omega
        omega
    · have hge : (l u).length ≤ i := Nat.le_of_not_gt hleft
      have hjlen : i - (l u).length < v.length := by
        have hsum : (l u ++ v).length = (l u).length + v.length := length_append
        omega
      have hget : (l u ++ v)[i] = v[i - (l u).length] := getElem_append_right hge
      have ihj := ih (i - (l u).length) hjlen
      rw [hget]
      constructor
      · intro hlt
        refine ihj.1 ?_
        omega
      · intro hgt
        refine ihj.2 ?_
        omega
  | _, @XWord.step_right u v hu hv => by
    have hp : PWord (u ++ r v) := ⟨XWord.step_right hu hv, hc⟩
    have huP := (PWord.of_step_right hu hv hp).1
    have hneg := (PWord.of_step_right hu hv hp).2
    have hneg1 : (-1 : ℤ) ∉ v := by simpa [count_eq_zero] using hneg
    have h0u : (0 : ℤ) ∈ u := hu.zero_mem
    have hidx : (u ++ r v).idxOf 0 = u.idxOf 0 := idxOf_append_of_mem h0u
    have ih (j : ℕ) (hj : j < u.length) := XWord.pword_sign hu huP.2 j hj
    by_cases hleft : i < u.length
    · have hget : (u ++ r v)[i] = u[i] := getElem_append_left hleft
      have ihj := ih i hleft
      rw [hget, hidx]
      exact ihj
    · have hge : u.length ≤ i := Nat.le_of_not_gt hleft
      have hjlen : i - u.length < (r v).length := by
        have hsum : (u ++ r v).length = u.length + (r v).length := length_append
        omega
      have hget : (u ++ r v)[i] = (r v)[i - u.length] := getElem_append_right hge
      have hx : v[v.length - 1 - (i - u.length)]'(Nat.sub_one_sub_lt_of_lt
          (by simpa [length_r] using hjlen)) ∈ v := getElem_mem _
      have hle := PWord.step_right_factor_nonneg hu hv hp hx
      rw [hget, getElem_r hjlen]
      constructor
      · intro hlt
        have : i < u.length := by
          have hidxu := idxOf_lt_length_of_mem h0u
          omega
        omega
      · intro _hgt
        omega

lemma PWord.getElem_neg_of_lt_idxOf {w : Word} (hw : PWord w) {i : ℕ}
    (hi : i < w.idxOf 0) :
    w[i]'(hi.trans hw.idxOf_lt_length) < 0 :=
  (XWord.pword_sign hw.1 hw.2 i (hi.trans hw.idxOf_lt_length)).1 hi

lemma PWord.getElem_pos_of_gt_idxOf {w : Word} (hw : PWord w) {i : ℕ}
    (h1 : w.idxOf 0 < i) (h2 : i < w.length) : 0 < w[i] :=
  (XWord.pword_sign hw.1 hw.2 i h2).2 h1

lemma PWord.idxOf_eq_zero_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) : w.idxOf 0 = 0 :=
  (idxOf_eq_zero_iff_head_eq hw.1.ne_nil).mpr hhead

lemma PWord.not_mem_neg_one_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) : (-1 : ℤ) ∉ w := by
  have hidx0 : w.idxOf 0 = 0 := PWord.idxOf_eq_zero_of_head_eq_zero hw hhead
  intro hmem
  have hne : w.idxOf (-1) ≠ 0 := by
    intro heq
    have : (0 : ℤ) = -1 :=
      (idxOf_inj hw.1.zero_mem).mp (hidx0.trans heq.symm)
    omega
  have hlt : w.idxOf (-1) < w.length := idxOf_lt_length_of_mem hmem
  have hpos : 0 < w[w.idxOf (-1)]'(hlt) :=
    PWord.getElem_pos_of_gt_idxOf hw (by omega) hlt
  have : w[w.idxOf (-1)]'(hlt) = -1 := getElem_idxOf _
  omega

lemma PWord.step_right_of_heads_eq_zero {u v : Word} (hu : PWord u) (hv : PWord v)
    (hu0 : u.head hu.1.ne_nil = 0) (hv0 : v.head hv.1.ne_nil = 0) :
    PWord (u ++ r v) := by
  have := hu0
  have hneg : (-1 : ℤ) ∉ v := PWord.not_mem_neg_one_of_head_eq_zero hv hv0
  have hx : XWord (u ++ r v) := XWord.step_right hu.1 hv.1
  have hcount : (u ++ r v).count 0 = 1 := by
    have hr0 : (r v).count 0 = 0 := by
      simpa [count_zero_r, count_eq_zero] using hneg
    simp [count_append, hu.2, hr0]
  exact ⟨hx, hcount⟩

lemma PWord.getLast_eq_one_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) (hlen : 2 ≤ w.length) :
    w.getLast hw.1.ne_nil = 1 := by
  have hidx : w.idxOf 0 = 0 := PWord.idxOf_eq_zero_of_head_eq_zero hw hhead
  have hlt : w.length - 1 < w.length := by omega
  have hpos : 0 < w[w.length - 1]'(hlt) :=
    PWord.getElem_pos_of_gt_idxOf hw (by omega) hlt
  have hgetLast : w.getLast hw.1.ne_nil = w[w.length - 1]'(hlt) :=
    getLast_eq_getElem hw.1.ne_nil
  have hlast := hw.1.getLast_eq_zero_or_one
  omega

lemma PWord.le_length_of_isRightParse_append_r {u v u' v' : Word}
    (hu : XWord u) (hv : PWord v) (h : IsRightParse (u ++ r v) u' v') :
    v.length ≤ v'.length := by
  have := hu
  have huX := h.1
  have hv'X := h.2.1
  have hsum := h.length_add
  have htot : (u ++ r v).length = u.length + v.length := by
    simp [length_r]
  have hlen' : u'.length + v'.length = u.length + v.length := by omega
  by_contra hlt
  have hvlt : v'.length < v.length := Nat.lt_of_not_ge hlt
  let k := u'.length - u.length
  have hkpos : 0 < k := by omega
  have hsucc : u'.length = u.length + k := by omega
  have htake : (u ++ r v).take u'.length = u ++ (r v).take k := by
    rw [hsucc, take_length_add_append]
  have hdrop : (u ++ r v).drop u'.length = (r v).drop k := by
    rw [hsucc, drop_length_add_append]
  let m := v.length - k
  have hsne : v.drop m ≠ [] := by
    simp [m, drop_eq_nil_iff]
    omega
  have hv'_eq : v' = v.take m := by
    have hr := h.drop
    have : r v' = r (v.take m) := by
      calc
        r v' = (u ++ r v).drop u'.length := hr.symm
        _ = (r v).drop k := hdrop
        _ = r (v.take (v.length - k)) := drop_r _ _
        _ = r (v.take m) := rfl
    exact r_injective this
  have h0take : (0 : ℤ) ∈ v.take m := by
    simpa [hv'_eq] using hv'X.zero_mem
  have hidxlt : v.idxOf 0 < m :=
    (mem_take_iff_idxOf_lt hv.1.zero_mem).mp h0take
  have hm_lt : m < v.length := by
    simp [drop_eq_nil_iff] at hsne
    omega
  have hheadpos : 0 < (v.drop m).head hsne := by
    rw [head_drop hsne]
    exact PWord.getElem_pos_of_gt_idxOf hv hidxlt hm_lt
  have h1le : 1 ≤ (v.drop m).head hsne := by omega
  have hnot : ¬ XWord (u ++ r (v.drop m)) :=
    not_xWord_append_r_of_one_le_head hsne h1le
  have hpre := h.take
  have hu_eq : u' = u ++ (r v).take k := hpre.symm.trans htake
  have hrk : (r v).take k = r (v.drop m) := take_r v k
  exact hnot (by simpa [hu_eq, hrk] using huX)

lemma PWord.isRightParse_cons_zero_r {v : Word} (hv : PWord v) :
    IsRightParse ([0] ++ r v) [0] v :=
  ⟨XWord.base, hv.1, rfl⟩

lemma PWord.eq_of_isRightParse_cons_zero_r {v u v' : Word} (hv : PWord v)
    (h : IsRightParse ([0] ++ r v) u v') : u = [0] ∧ v' = v := by
  have huX := h.1
  have hv'X := h.2.1
  have hw := h.2.2
  have hk : u.length = 1 ∨ 2 ≤ u.length := by
    have := h.pos_left
    omega
  rcases hk with hk | hk
  · have hu0 : u = [0] :=
      match u, huX with
      | _, .base => rfl
      | _, @XWord.step_left u0 v0 hu0 hv0 => by
          have hsum : u0.length + v0.length = 1 := by simpa [l] using hk
          have := hu0.length_pos
          have := hv0.length_pos
          omega
      | _, @XWord.step_right u0 v0 hu0 hv0 => by
          have hsum : u0.length + v0.length = 1 := by simpa [r] using hk
          have := hu0.length_pos
          have := hv0.length_pos
          omega
    have hr : r v = r v' := by
      have := hw
      simp [hu0] at this
      exact this
    exact ⟨hu0, r_injective hr.symm⟩
  · let k := u.length - 1
    have hsucc : u.length = Nat.succ k := by omega
    have htake : ([0] ++ r v).take u.length = 0 :: (r v).take k := by
      rw [show ([0] ++ r v) = 0 :: r v from rfl, hsucc, take_succ_cons]
    have hdrop : ([0] ++ r v).drop u.length = (r v).drop k := by
      rw [show ([0] ++ r v) = 0 :: r v from rfl, hsucc, drop_succ_cons]
    have hm_add : k + v'.length = v.length := by
      have hsum := h.length_add
      have : ([0] ++ r v).length = v.length + 1 := by simp [length_r]
      omega
    have hule : k ≤ v.length := by omega
    let m := v.length - k
    have hsne : v.drop m ≠ [] := by
      have : 0 < k := by omega
      simp [m, drop_eq_nil_iff]
      omega
    have hv'_eq : v' = v.take m := by
      have hr := h.drop
      have : r v' = r (v.take m) := by
        calc
          r v' = ([0] ++ r v).drop u.length := hr.symm
          _ = (r v).drop k := hdrop
          _ = r (v.take (v.length - k)) := drop_r _ _
          _ = r (v.take m) := rfl
      exact r_injective this
    have h0take : (0 : ℤ) ∈ v.take m := by
      simpa [hv'_eq] using hv'X.zero_mem
    have hidxlt : v.idxOf 0 < m :=
      (mem_take_iff_idxOf_lt hv.1.zero_mem).mp h0take
    have hm_lt : m < v.length := by
      simp [drop_eq_nil_iff] at hsne
      omega
    have hheadpos : 0 < (v.drop m).head hsne := by
      rw [head_drop hsne]
      exact PWord.getElem_pos_of_gt_idxOf hv hidxlt hm_lt
    have h1le : 1 ≤ (v.drop m).head hsne := by omega
    have hnot : ¬ XWord ([0] ++ r (v.drop m)) :=
      not_xWord_cons_zero_r_of_one_le_head hsne h1le
    have hu_eq : u = [0] ++ r (v.drop m) := by
      have hpre := h.take
      have : u = 0 :: (r v).take k := by
        calc
          u = ([0] ++ r v).take u.length := hpre.symm
          _ = 0 :: (r v).take k := htake
      rw [this, take_r]
      have : v.length - k = m := rfl
      simp [this]
    exact (hnot (hu_eq ▸ huX)).elim

lemma count_zero_rho (w : Word) : (rho w).count 0 = w.count 0 := by
  simp [rho, count_eq_countP, countP_map]
  congr 1
  ext x
  simp

lemma PWord.rho {w : Word} (hw : PWord w) : PWord (rho w) :=
  ⟨hw.1.rho_mem, (count_zero_rho w).trans hw.2⟩

lemma XWord.take_idxOf_concat_zero {w : Word} (hw : XWord w) (hc : w.count 0 = 1) :
    PWord (w.take (w.idxOf 0) ++ [0]) :=
  match w, hw with
  | _, .base => by
    simpa [idxOf_cons_self] using PWord.base
  | _, @XWord.step_left u v hu hv => by
    have hp : PWord (l u ++ v) := ⟨XWord.step_left hu hv, hc⟩
    have hvP := (PWord.of_step_left hu hv hp).1
    have hones := (PWord.of_step_left hu hv hp).2
    have h1u : (1 : ℤ) ∉ u := by simpa [count_eq_zero] using hones
    have h0lu : (0 : ℤ) ∉ l u := fun hmem => h1u (mem_l_iff.mp hmem)
    have hidx : (l u ++ v).idxOf 0 = (l u).length + v.idxOf 0 :=
      idxOf_append_of_notMem h0lu
    have ih := XWord.take_idxOf_concat_zero hv hvP.2
    have htake : (l u ++ v).take ((l u ++ v).idxOf 0) ++ [0] =
        l u ++ (v.take (v.idxOf 0) ++ [0]) := by
      rw [hidx, take_length_add_append, append_assoc]
    have hx : XWord (l u ++ (v.take (v.idxOf 0) ++ [0])) :=
      XWord.step_left hu ih.1
    have hcount : (l u ++ (v.take (v.idxOf 0) ++ [0])).count 0 = 1 := by
      have hlu0 : (l u).count 0 = 0 := by
        simpa [count_zero_l] using hones
      simp [count_append, hlu0, ih.2]
    exact htake ▸ ⟨hx, hcount⟩
  | _, @XWord.step_right u v hu hv => by
    have hp : PWord (u ++ r v) := ⟨XWord.step_right hu hv, hc⟩
    have huP := (PWord.of_step_right hu hv hp).1
    have h0u : (0 : ℤ) ∈ u := hu.zero_mem
    have hidx : (u ++ r v).idxOf 0 = u.idxOf 0 := idxOf_append_of_mem h0u
    have ih := XWord.take_idxOf_concat_zero hu huP.2
    have hklt : u.idxOf 0 ≤ u.length := (idxOf_lt_length_of_mem h0u).le
    have htake : (u ++ r v).take ((u ++ r v).idxOf 0) ++ [0] =
        u.take (u.idxOf 0) ++ [0] := by
      rw [hidx, take_append_of_le_length hklt]
    exact htake ▸ ih

lemma PWord.take_idxOf_concat_zero {w : Word} (hw : PWord w) :
    PWord (w.take (w.idxOf 0) ++ [0]) :=
  XWord.take_idxOf_concat_zero hw.1 hw.2

lemma XWord.cons_zero_drop_succ_idxOf {w : Word} (hw : XWord w) (hc : w.count 0 = 1) :
    PWord (0 :: w.drop (w.idxOf 0 + 1)) :=
  match w, hw with
  | _, .base => by
    simpa [idxOf_cons_self] using PWord.base
  | _, @XWord.step_left u v hu hv => by
    have hp : PWord (l u ++ v) := ⟨XWord.step_left hu hv, hc⟩
    have hvP := (PWord.of_step_left hu hv hp).1
    have hones := (PWord.of_step_left hu hv hp).2
    have h1u : (1 : ℤ) ∉ u := by simpa [count_eq_zero] using hones
    have h0lu : (0 : ℤ) ∉ l u := fun hmem => h1u (mem_l_iff.mp hmem)
    have hidx : (l u ++ v).idxOf 0 = (l u).length + v.idxOf 0 :=
      idxOf_append_of_notMem h0lu
    have ih := XWord.cons_zero_drop_succ_idxOf hv hvP.2
    have hdrop : 0 :: (l u ++ v).drop ((l u ++ v).idxOf 0 + 1) =
        0 :: v.drop (v.idxOf 0 + 1) := by
      rw [hidx, Nat.add_assoc, drop_length_add_append]
    exact hdrop ▸ ih
  | _, @XWord.step_right u v hu hv => by
    have hp : PWord (u ++ r v) := ⟨XWord.step_right hu hv, hc⟩
    have huP := (PWord.of_step_right hu hv hp).1
    have hneg := (PWord.of_step_right hu hv hp).2
    have h0u : (0 : ℤ) ∈ u := hu.zero_mem
    have hidx : (u ++ r v).idxOf 0 = u.idxOf 0 := idxOf_append_of_mem h0u
    have ih := XWord.cons_zero_drop_succ_idxOf hu huP.2
    have hklt : u.idxOf 0 < u.length := idxOf_lt_length_of_mem h0u
    have hle : u.idxOf 0 + 1 ≤ u.length := Nat.succ_le_of_lt hklt
    have hdrop : 0 :: (u ++ r v).drop ((u ++ r v).idxOf 0 + 1) =
        (0 :: u.drop (u.idxOf 0 + 1)) ++ r v := by
      rw [hidx, drop_append_of_le_length hle, cons_append]
    have hx : XWord ((0 :: u.drop (u.idxOf 0 + 1)) ++ r v) :=
      XWord.step_right ih.1 hv
    have hcount : ((0 :: u.drop (u.idxOf 0 + 1)) ++ r v).count 0 = 1 := by
      have hr0 : (r v).count 0 = 0 := by
        simpa [count_zero_r] using hneg
      rw [count_append, ih.2, hr0]
    exact hdrop ▸ ⟨hx, hcount⟩

lemma PWord.cons_zero_drop_succ_idxOf {w : Word} (hw : PWord w) :
    PWord (0 :: w.drop (w.idxOf 0 + 1)) :=
  XWord.cons_zero_drop_succ_idxOf hw.1 hw.2

lemma PWord.take_idxOf_concat_zero_append_drop {w : Word} (hw : PWord w) :
    w.take (w.idxOf 0) ++ [0] ++ w.drop (w.idxOf 0 + 1) = w := by
  have hlt := hw.idxOf_lt_length
  have h0 := hw.getElem_idxOf_zero
  have htake : w.take (w.idxOf 0 + 1) = w.take (w.idxOf 0) ++ [0] := by
    simpa [h0] using take_succ_eq_append_getElem hlt
  calc
    w.take (w.idxOf 0) ++ [0] ++ w.drop (w.idxOf 0 + 1) =
        w.take (w.idxOf 0 + 1) ++ w.drop (w.idxOf 0 + 1) := by
      simp [htake]
    _ = w := take_append_drop _ _

lemma exists_left_parse_of_head_eq_neg_one {w : Word} (hw : XWord w)
    (h : w.head hw.ne_nil = -1) :
    ∃ u v, IsLeftParse w u v :=
  match w, hw with
  | _, .base => by simp at h
  | _, @XWord.step_left u v hu hv => ⟨u, v, hu, hv, rfl⟩
  | _, @XWord.step_right u v hu hv => by
    have hu_ne := hu.ne_nil
    have hhead : u.head hu_ne = -1 := by
      have h' := head_append_of_ne_nil (l := u) (l' := r v)
        (w₁ := XWord.ne_nil (XWord.step_right hu hv)) hu_ne
      exact h' ▸ h
    obtain ⟨u', v', hu', hv', hw'⟩ :=
      exists_left_parse_of_head_eq_neg_one hu hhead
    refine ⟨u', v' ++ r v, hu', XWord.step_right hv' hv, ?_⟩
    simp [hw']

lemma XWord.concat_one {u : Word} (hu : XWord u) : XWord (u ++ [1]) := by
  simpa [r_zero] using XWord.step_right hu XWord.base

lemma XWord.concat_neg_one {u : Word} (hu : XWord u) : XWord ([-1] ++ u) := by
  simpa [l_zero] using XWord.step_left XWord.base hu

lemma XWord.cons_zero_of_head_eq_neg_one {w : Word} (hw : XWord w)
    (h : w.head hw.ne_nil = -1) : XWord (0 :: w) := by
  obtain ⟨u, v, hu, hv, hw'⟩ := exists_left_parse_of_head_eq_neg_one hw h
  have : 0 :: w = l (u ++ [1]) ++ v := by
    rw [hw', l_concat_one, cons_append]
  rw [this]
  exact XWord.step_left (XWord.concat_one hu) hv

lemma exists_right_parse_of_getLast_eq_one {w : Word} (hw : XWord w)
    (h : w.getLast hw.ne_nil = 1) :
    ∃ u v, IsRightParse w u v := by
  have hρ := XWord.rho_mem hw
  have hhead : (rho w).head (XWord.ne_nil hρ) = -1 := by
    have h1 : (rho w).head (rho_ne_nil hw.ne_nil) = - w.getLast hw.ne_nil :=
      rho_head hw.ne_nil
    have h2 : (rho w).head (XWord.ne_nil hρ) =
        (rho w).head (rho_ne_nil hw.ne_nil) := rfl
    rw [h2, h1, h]
  obtain ⟨u, v, hu, hv, hparse⟩ := exists_left_parse_of_head_eq_neg_one hρ hhead
  refine ⟨rho v, rho u, XWord.rho_mem hv, XWord.rho_mem hu, ?_⟩
  have hρw := congrArg rho hparse
  simpa [rho_rho, rho_append, rho_l] using hρw

lemma PWord.exists_right_parse_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) (hlen : 2 ≤ w.length) :
    ∃ u v, IsRightParse w u v :=
  exists_right_parse_of_getLast_eq_one hw.1
    (PWord.getLast_eq_one_of_head_eq_zero hw hhead hlen)

lemma PWord.head_eq_zero_of_isRightParse {u v : Word} (hu : XWord u)
    (hv : XWord v) (hhead : (u ++ r v).head (XWord.ne_nil (XWord.step_right hu hv)) = 0) :
    u.head hu.ne_nil = 0 := by
  have := head_append_of_ne_nil (l := u) (l' := r v)
    (w₁ := XWord.ne_nil (XWord.step_right hu hv)) hu.ne_nil
  exact this ▸ hhead

lemma PWord.exists_shortest_right_parse_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) (hlen : 2 ≤ w.length) :
    ∃ u v, IsRightParse w u v ∧
      ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length :=
  exists_shortest_right_parse
    (PWord.exists_right_parse_of_head_eq_zero hw hhead hlen)

lemma exists_concat_split_of_append {a b : Word} (ha : XWord a) (hb : XWord b) :
    ∃ k, 0 < k ∧ k < (a ++ b).length ∧ XWord ((a ++ b).take k) ∧
      XWord ((a ++ b).drop k) := by
  refine ⟨a.length, ha.length_pos, ?_, ?_, ?_⟩
  · have := hb.length_pos
    simp
    omega
  · simpa using ha
  · simpa using hb

lemma IsRightParse.of_concat_remainder {w u v v1 v2 : Word}
    (h : IsRightParse w u v) (hv1 : XWord v1) (hv2 : XWord v2)
    (heq : v = v1 ++ v2) :
    IsRightParse w (u ++ r v2) v1 := by
  rcases h with ⟨hu, hv, hw⟩
  subst heq
  refine ⟨XWord.step_right hu hv2, hv1, ?_⟩
  simp [hw, r_append]

-- A Xia word with at least two zeros is the concatenation of two Xia words.
lemma XWord.exists_concat_split_of_length :
    ∀ (n : ℕ) (w : Word), w.length = n → XWord w → 2 ≤ w.count 0 →
      ∃ k, 0 < k ∧ k < w.length ∧ XWord (w.take k) ∧ XWord (w.drop k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen hw hc
    have recRight : ∀ {w : Word}, XWord w → w.length = n → 2 ≤ w.count 0 →
        (∃ u v, IsRightParse w u v) →
        ∃ k, 0 < k ∧ k < w.length ∧ XWord (w.take k) ∧ XWord (w.drop k) := by
      intro w hw hwlen hc hp
      obtain ⟨u, v, hp, hmin⟩ := exists_shortest_right_parse hp
      have hsum : w.count 0 = u.count 0 + v.count (-1) := by
        simp [hp.2.2, count_append, count_zero_r]
      have hu0 := hp.1.count_zero_pos
      by_cases h2 : 2 ≤ u.count 0
      · have hult : u.length < n := by
          have := hp.left_lt_length
          omega
        obtain ⟨k, hk0, hkl, htk, hdk⟩ := ih u.length hult u rfl hp.1 h2
        have hk_le : k ≤ u.length := hkl.le
        have htake : w.take k = u.take k := by
          rw [hp.2.2, take_append_of_le_length hk_le]
        have hdrop : w.drop k = u.drop k ++ r v := by
          rw [hp.2.2, drop_append_of_le_length hk_le]
        refine ⟨k, hk0, ?_, htake ▸ htk, ?_⟩
        · have := hp.left_lt_length
          omega
        · rw [hdrop]
          exact XWord.step_right hdk hp.2.1
      · have huP : u.count 0 = 1 := by omega
        have hvneg : 1 ≤ v.count (-1) := by omega
        have hmem : (-1 : ℤ) ∈ v := count_pos_iff.mp (by omega)
        have hvhead := hp.2.1.head_eq_neg_one_or_zero
        rcases hvhead with hneg1 | h0
        · obtain ⟨a, b, ha, hb, hveq⟩ :=
            exists_left_parse_of_head_eq_neg_one hp.2.1 hneg1
          have hw_eq : w = (u ++ r b) ++ a := by
            rw [hp.2.2, hveq, r_append, r_l, append_assoc]
          rw [hw_eq]
          exact exists_concat_split_of_append (XWord.step_right hp.1 hb) ha
        · have hne1 : v.count 0 ≠ 1 := by
            intro hcnt
            exact PWord.not_mem_neg_one_of_head_eq_zero ⟨hp.2.1, hcnt⟩ h0 hmem
          have hv2 : 2 ≤ v.count 0 := by
            have := hp.2.1.count_zero_pos
            omega
          have hvlt : v.length < n := by
            have := hp.pos_left
            have := hp.length_add
            omega
          obtain ⟨k, hk0, hkl, htk, hdk⟩ := ih v.length hvlt v rfl hp.2.1 hv2
          have hparse' : IsRightParse w (u ++ r (v.drop k)) (v.take k) :=
            IsRightParse.of_concat_remainder hp htk hdk (take_append_drop k v).symm
          have hle := hmin (u ++ r (v.drop k)) (v.take k) hparse'
          have htklen : (v.take k).length = k := by
            simp [length_take]
            omega
          omega
    by_cases hp : ∃ u v, IsRightParse w u v
    · exact recRight hw hlen hc hp
    · have hρ := hw.rho_mem
      have hρc : 2 ≤ (rho w).count 0 := by simpa [count_zero_rho] using hc
      have hρlen : (rho w).length = n := by simpa [length_rho] using hlen
      have hρp : ∃ u v, IsRightParse (rho w) u v := by
        cases hw with
        | base =>
          have : ([0] : Word).count 0 = 1 := by decide
          omega
        | step_right hu hv =>
          exact (hp ⟨_, _, hu, hv, rfl⟩).elim
        | step_left hu hv =>
          refine ⟨rho _, rho _, XWord.rho_mem hv, XWord.rho_mem hu, ?_⟩
          simp [rho_append, rho_l]
      obtain ⟨k, hk0, hkl, htk, hdk⟩ := recRight hρ hρlen hρc hρp
      have hw_eq : w = rho ((rho w).drop k) ++ rho ((rho w).take k) := by
        calc
          w = rho (rho w) := (rho_rho w).symm
          _ = rho ((rho w).take k ++ (rho w).drop k) := by rw [take_append_drop]
          _ = rho ((rho w).drop k) ++ rho ((rho w).take k) := rho_append _ _
      have hsplit := exists_concat_split_of_append (XWord.rho_mem hdk) (XWord.rho_mem htk)
      rw [← hw_eq] at hsplit
      exact hsplit

lemma XWord.exists_concat_split {w : Word} (hw : XWord w) (hc : 2 ≤ w.count 0) :
    ∃ k, 0 < k ∧ k < w.length ∧ XWord (w.take k) ∧ XWord (w.drop k) :=
  XWord.exists_concat_split_of_length w.length w rfl hw hc

lemma XWord.of_isRightParse_shortest {w u v : Word}
    (h : IsRightParse w u v)
    (hmin : ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length) :
    PWord v := by
  refine ⟨h.2.1, ?_⟩
  by_contra hne
  have hc : 2 ≤ v.count 0 := by
    have := h.2.1.count_zero_pos
    omega
  obtain ⟨k, hk0, hkl, htk, hdk⟩ := XWord.exists_concat_split h.2.1 hc
  have hparse' : IsRightParse w (u ++ r (v.drop k)) (v.take k) :=
    IsRightParse.of_concat_remainder h htk hdk (take_append_drop k v).symm
  have hle := hmin (u ++ r (v.drop k)) (v.take k) hparse'
  have htklen : (v.take k).length = k := by
    simp [length_take]
    omega
  omega

lemma PWord.of_isRightParse_shortest {w u v : Word} (_hw : PWord w)
    (h : IsRightParse w u v)
    (hmin : ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length) :
    PWord v :=
  XWord.of_isRightParse_shortest h hmin

lemma PWord.shortest_right_parse_factors {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) (hlen : 2 ≤ w.length) :
    ∃ u v, IsRightParse w u v ∧ PWord u ∧ PWord v ∧
      ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length := by
  obtain ⟨u, v, hp, hmin⟩ :=
    PWord.exists_shortest_right_parse_of_head_eq_zero hw hhead hlen
  refine ⟨u, v, hp, ?_, PWord.of_isRightParse_shortest hw hp hmin, hmin⟩
  exact (PWord.of_step_right hp.1 hp.2.1 (hp.2.2 ▸ hw)).1

lemma PWord.remainder_head_eq_zero {w u v : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) (hlen : 2 ≤ w.length)
    (hp : IsRightParse w u v) :
    v.head hp.2.1.ne_nil = 0 := by
  have hlast := PWord.getLast_eq_one_of_head_eq_zero hw hhead hlen
  have hne_r := r_ne_nil hp.2.1.ne_nil
  have hgl : (u ++ r v).getLast (XWord.ne_nil (XWord.step_right hp.1 hp.2.1)) =
      (r v).getLast hne_r :=
    getLast_append_of_right_ne_nil _ _ hne_r
  have hgl' : w.getLast hw.1.ne_nil =
      (u ++ r v).getLast (XWord.ne_nil (XWord.step_right hp.1 hp.2.1)) := by
    simp [hp.2.2]
  have : (r v).getLast hne_r = v.head hp.2.1.ne_nil + 1 := getLast_r hp.2.1.ne_nil
  omega

lemma PWord.eq_of_step_right {u v u' v' : Word}
    (hu : PWord u) (hv : PWord v) (hu' : PWord u') (hv' : PWord v')
    (h : u ++ r v = u' ++ r v') : u = u' ∧ v = v' := by
  have hp : IsRightParse (u ++ r v) u v := ⟨hu.1, hv.1, rfl⟩
  have hp' : IsRightParse (u ++ r v) u' v' := ⟨hu'.1, hv'.1, h⟩
  have hle := PWord.le_length_of_isRightParse_append_r hu.1 hv hp'
  have hp2 : IsRightParse (u' ++ r v') u v := ⟨hu.1, hv.1, h.symm⟩
  have hle' := PWord.le_length_of_isRightParse_append_r hu'.1 hv' hp2
  have hvlen : v.length = v'.length := Nat.le_antisymm hle hle'
  have hsum := hp.length_add
  have htot : (u ++ r v).length = u'.length + v'.length := by
    rw [h]
    simp [length_r]
  have hulen : u.length = u'.length := by omega
  exact eq_of_right_parse_eq h hulen

lemma head_eq_zero_iff_head? {w : Word} (h : w ≠ []) :
    w.head h = 0 ↔ w.head? = some 0 := by
  cases w with
  | nil => exact (h rfl).elim
  | cons a t => simp

-- Start-with-0 unique-zero Xia words. Experimentally `|Right_n| = C_{n-1}`.
def RightWord (w : Word) : Prop :=
  PWord w ∧ w.head? = some 0

lemma RightWord.pWord {w : Word} (h : RightWord w) : PWord w := h.1

lemma RightWord.xWord {w : Word} (h : RightWord w) : XWord w := h.1.1

lemma RightWord.head_eq_zero {w : Word} (h : RightWord w) :
    w.head h.xWord.ne_nil = 0 :=
  (head_eq_zero_iff_head? h.xWord.ne_nil).mpr h.2

lemma RightWord.of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) : RightWord w :=
  ⟨hw, (head_eq_zero_iff_head? hw.1.ne_nil).mp hhead⟩

lemma length_append_r (u v : Word) : (u ++ r v).length = u.length + v.length := by
  simp [length_r]

lemma RightWord.of_step_right {u v : Word} (hu : RightWord u) (hv : RightWord v) :
    RightWord (u ++ r v) := by
  have hp :=
    PWord.step_right_of_heads_eq_zero hu.pWord hv.pWord hu.head_eq_zero hv.head_eq_zero
  have hhead : (u ++ r v).head hp.1.ne_nil = 0 := by
    have h' := head_append_of_ne_nil (l := u) (l' := r v)
      (w₁ := hp.1.ne_nil) hu.xWord.ne_nil
    exact h' ▸ hu.head_eq_zero
  exact RightWord.of_head_eq_zero hp hhead

lemma RightWord.exists_step_right {w : Word} (hw : RightWord w) (hlen : 2 ≤ w.length) :
    ∃ u v, RightWord u ∧ RightWord v ∧ w = u ++ r v := by
  have hhead := hw.head_eq_zero
  obtain ⟨u, v, hp, hu, hv, _⟩ :=
    PWord.shortest_right_parse_factors hw.pWord hhead hlen
  have hu0 : u.head hu.1.ne_nil = 0 :=
    PWord.head_eq_zero_of_isRightParse hp.1 hp.2.1 (by
      have h' : (u ++ r v).head (XWord.ne_nil (XWord.step_right hp.1 hp.2.1)) =
          w.head hw.xWord.ne_nil := by
        simp [hp.2.2]
      exact h' ▸ hhead)
  have hv0 := PWord.remainder_head_eq_zero hw.pWord hhead hlen hp
  exact ⟨u, v, RightWord.of_head_eq_zero hu hu0, RightWord.of_head_eq_zero hv hv0, hp.2.2⟩

def rightN (n : ℕ) : Set Word :=
  {w | RightWord w ∧ w.length = n}

lemma rightN_subset_xN (n : ℕ) : rightN n ⊆ xN n :=
  fun _ hw => ⟨hw.1.xWord, hw.2⟩

lemma rightN_finite (n : ℕ) : (rightN n).Finite :=
  (xN_finite n).subset (rightN_subset_xN n)

noncomputable def rightNFinset (n : ℕ) : Finset Word :=
  (rightN_finite n).toFinset

lemma mem_rightNFinset {n : ℕ} {w : Word} :
    w ∈ rightNFinset n ↔ w ∈ rightN n :=
  Set.Finite.mem_toFinset (rightN_finite n)

lemma ncard_rightN_eq_card (n : ℕ) :
    (rightN n).ncard = (rightNFinset n).card :=
  Set.ncard_eq_toFinset_card _ (rightN_finite n)

lemma XWord.eq_base_of_length_one {w : Word} (hw : XWord w) (h : w.length = 1) :
    w = [0] :=
  match w, hw with
  | _, .base => rfl
  | _, @XWord.step_left u v hu hv => by
    have : 2 ≤ (l u ++ v).length := by
      simp [l]
      have := hu.length_pos
      have := hv.length_pos
      omega
    omega
  | _, @XWord.step_right u v hu hv => by
    have : 2 ≤ (u ++ r v).length := by
      simp [r]
      have := hu.length_pos
      have := hv.length_pos
      omega
    omega

lemma rightN_one : rightN 1 = {[0]} := by
  ext w
  constructor
  · intro hw
    have : w = [0] := XWord.eq_base_of_length_one hw.1.xWord hw.2
    simp [this]
  · rintro rfl
    refine ⟨⟨PWord.base, ?_⟩, rfl⟩
    simp

lemma ncard_rightN_one : (rightN 1).ncard = catalan 0 := by
  have := rightN_finite 1
  rw [rightN_one, Set.ncard_singleton, catalan_zero]

lemma disjoint_rightNFinset_product {i j k l : ℕ} (hij : i ≠ j) :
    Disjoint (rightNFinset i ×ˢ rightNFinset k)
      (rightNFinset j ×ˢ rightNFinset l) := by
  refine Finset.disjoint_iff_ne.mpr ?_
  intro p hp q hq hpeq
  have hi : p.1.length = i := (mem_rightNFinset.mp (Finset.mem_product.mp hp).1).2
  have hj : q.1.length = j := (mem_rightNFinset.mp (Finset.mem_product.mp hq).1).2
  have : p.1.length = q.1.length := congrArg List.length (congrArg Prod.fst hpeq)
  omega

noncomputable def rightPairs (n : ℕ) : Finset (Word × Word) :=
  (Finset.Icc 1 n).biUnion fun i =>
    rightNFinset i ×ˢ rightNFinset (n + 1 - i)

lemma mem_rightPairs {n : ℕ} {p : Word × Word} :
    p ∈ rightPairs n ↔
      ∃ i ∈ Finset.Icc 1 n, p.1 ∈ rightN i ∧ p.2 ∈ rightN (n + 1 - i) := by
  simp [rightPairs, Finset.mem_biUnion, Finset.mem_product, mem_rightNFinset]

lemma RightWord.of_mem_rightPairs {n : ℕ} {p : Word × Word} (hp : p ∈ rightPairs n) :
    RightWord p.1 ∧ RightWord p.2 := by
  obtain ⟨i, _, hu, hv⟩ := mem_rightPairs.mp hp
  exact ⟨hu.1, hv.1⟩

lemma card_rightPairs (n : ℕ) :
    (rightPairs n).card =
      ∑ i ∈ Finset.Icc 1 n,
        (rightNFinset i).card * (rightNFinset (n + 1 - i)).card := by
  have hdisj : (Finset.Icc 1 n : Set ℕ).PairwiseDisjoint
      (fun i => rightNFinset i ×ˢ rightNFinset (n + 1 - i)) := by
    intro i _ j _ hij
    exact disjoint_rightNFinset_product hij
  rw [rightPairs, Finset.card_biUnion hdisj]
  simp [Finset.card_product]

lemma injOn_append_r_rightPairs (n : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1 ++ r p.2) (rightPairs n) := by
  intro p hp q hq heq
  have hpR := RightWord.of_mem_rightPairs hp
  have hqR := RightWord.of_mem_rightPairs hq
  obtain ⟨h1, h2⟩ :=
    PWord.eq_of_step_right hpR.1.pWord hpR.2.pWord hqR.1.pWord hqR.2.pWord heq
  exact Prod.ext h1 h2

lemma image_rightPairs (n : ℕ) (hn : 1 ≤ n) :
    (rightPairs n).image (fun p => p.1 ++ r p.2) = rightNFinset (n + 1) := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, hi, hu, hv⟩ := mem_rightPairs.mp hp
    have hwR : RightWord (p.1 ++ r p.2) := RightWord.of_step_right hu.1 hv.1
    have hlen : (p.1 ++ r p.2).length = n + 1 := by
      have hi1 : 1 ≤ i ∧ i ≤ n := Finset.mem_Icc.mp hi
      rw [length_append_r, hu.2, hv.2]
      omega
    exact mem_rightNFinset.mpr ⟨hwR, hlen⟩
  · intro hw
    have hw' := mem_rightNFinset.mp hw
    have hlenw : w.length = n + 1 := hw'.2
    have hlen2 : 2 ≤ w.length := by omega
    obtain ⟨u, v, hu, hv, heq⟩ := RightWord.exists_step_right hw'.1 hlen2
    have hsum : u.length + v.length = n + 1 := by
      have hlen := congrArg List.length heq
      rw [length_append_r] at hlen
      omega
    have hu_pos := hu.xWord.length_pos
    have hv_pos := hv.xWord.length_pos
    have hi : u.length ∈ Finset.Icc 1 n := by
      simp [Finset.mem_Icc]
      omega
    have huN : u ∈ rightN u.length := ⟨hu, rfl⟩
    have hvN : v ∈ rightN (n + 1 - u.length) := ⟨hv, by omega⟩
    refine Finset.mem_image.mpr ⟨(u, v), ?_, heq.symm⟩
    exact mem_rightPairs.mpr ⟨u.length, hi, huN, hvN⟩

lemma ncard_rightN_succ (n : ℕ) (hn : 1 ≤ n) :
    (rightN (n + 1)).ncard =
      ∑ i ∈ Finset.Icc 1 n, (rightN i).ncard * (rightN (n + 1 - i)).ncard := by
  have himg := image_rightPairs n hn
  have hinj := injOn_append_r_rightPairs n
  have hcard : (rightNFinset (n + 1)).card = (rightPairs n).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  rw [ncard_rightN_eq_card, hcard, card_rightPairs]
  simp [ncard_rightN_eq_card]

lemma Icc_one_eq_map_succ (n : ℕ) :
    Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
  ext k
  constructor
  · intro hk
    rcases Finset.mem_Icc.mp hk with ⟨h1, h2⟩
    refine Finset.mem_map.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simp [Nat.succ_eq_add_one]
    omega
  · intro hk
    rcases Finset.mem_map.mp hk with ⟨i, hi, hk'⟩
    have hk1 : k = i + 1 := by
      simpa [Nat.succ_eq_add_one] using hk'.symm
    have : i < n := Finset.mem_range.mp hi
    simp [Finset.mem_Icc, hk1]
    omega

lemma sum_catalan_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, catalan (i - 1) * catalan (n - i) = catalan n := by
  rw [Icc_one_eq_map_succ, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
  have hfun : ∀ i ∈ Finset.range n,
      catalan (i + 1 - 1) * catalan (n - (i + 1)) =
        catalan i * catalan (n - 1 - i) := by
    intro i hi
    have : i < n := Finset.mem_range.mp hi
    have h1 : i + 1 - 1 = i := by omega
    have h2 : n - (i + 1) = n - 1 - i := by omega
    simp [h1, h2]
  rw [Finset.sum_congr rfl hfun]
  have hn' : n = n - 1 + 1 := by omega
  rw [show catalan n = catalan (n - 1 + 1) from congrArg catalan hn',
    catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => catalan x * catalan y)]
  have hsucc : (n - 1).succ = n := by
    rw [Nat.succ_eq_add_one]
    exact hn'.symm
  rw [hsucc]

lemma ncard_rightN_succ_eq_catalan :
    ∀ n : ℕ, (rightN (n + 1)).ncard = catalan n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ncard_rightN_one
    | succ n =>
      rw [ncard_rightN_succ (n + 1) (Nat.succ_pos _)]
      have hsum :
          ∑ i ∈ Finset.Icc 1 (n + 1),
              (rightN i).ncard * (rightN (n + 1 + 1 - i)).ncard =
            ∑ i ∈ Finset.Icc 1 (n + 1), catalan (i - 1) * catalan (n + 1 - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hile : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
        have h1 : (rightN i).ncard = catalan (i - 1) := by
          have hlt1 : i - 1 < n + 1 :=
            Nat.lt_succ_of_le (by
              have h := Nat.sub_le_sub_right hile 1
              simpa using h)
          convert ih (i - 1) hlt1
          exact (Nat.sub_add_cancel hi1).symm
        have h2 : (rightN (n + 2 - i)).ncard = catalan (n + 1 - i) := by
          have hlt2 : n + 1 - i < n + 1 := Nat.sub_lt (Nat.succ_pos _) hi1
          rw [Nat.succ_sub hile]
          exact ih (n + 1 - i) hlt2
        have hidx : n + 1 + 1 - i = n + 2 - i := by omega
        rw [h1, hidx, h2]
      rw [hsum, sum_catalan_Icc (n + 1) (Nat.succ_pos _)]

lemma ncard_rightN_eq_catalan {n : ℕ} (hn : 1 ≤ n) :
    (rightN n).ncard = catalan (n - 1) := by
  convert ncard_rightN_succ_eq_catalan (n - 1)
  exact (Nat.sub_add_cancel hn).symm

lemma XWord.append_zero_of_getLast_eq_one {w : Word} (hw : XWord w)
    (h : w.getLast hw.ne_nil = 1) : XWord (w ++ [0]) := by
  obtain ⟨u, v, hu, hv, hw'⟩ := exists_right_parse_of_getLast_eq_one hw h
  have : w ++ [0] = u ++ r ([-1] ++ v) := by
    rw [hw', r_concat_neg_one, append_assoc]
  rw [this]
  exact XWord.step_right hu (XWord.concat_neg_one hv)

-- Small lengths

lemma xN_one : xN 1 = {[0]} := by
  ext w
  constructor
  · intro hw
    exact XWord.eq_base_of_length_one hw.1 hw.2
  · rintro rfl
    exact ⟨XWord.base, rfl⟩

lemma ncard_xN_one : (xN 1).ncard = a 0 := by
  have := xN_finite 1
  rw [xN_one, Set.ncard_singleton, a_0]

lemma XWord.eq_of_length_two {w : Word} (hw : XWord w) (h : w.length = 2) :
    w = [-1, 0] ∨ w = [0, 1] :=
  match w, hw with
  | _, .base => by simp at h
  | _, @XWord.step_left u v hu hv => by
    have hsum : u.length + v.length = 2 := by
      simpa [l] using h
    have hu1 : u.length = 1 := by
      have := hu.length_pos
      have := hv.length_pos
      omega
    have hv1 : v.length = 1 := by omega
    have hu0 := XWord.eq_base_of_length_one hu hu1
    have hv0 := XWord.eq_base_of_length_one hv hv1
    subst u
    subst v
    simp [l]
  | _, @XWord.step_right u v hu hv => by
    have hsum : u.length + v.length = 2 := by
      simpa [r] using h
    have hu1 : u.length = 1 := by
      have := hu.length_pos
      have := hv.length_pos
      omega
    have hv1 : v.length = 1 := by omega
    have hu0 := XWord.eq_base_of_length_one hu hu1
    have hv0 := XWord.eq_base_of_length_one hv hv1
    subst u
    subst v
    simp [r]

lemma xN_two : xN 2 = {[-1, 0], [0, 1]} := by
  ext w
  constructor
  · intro hw
    rcases XWord.eq_of_length_two hw.1 hw.2 with h | h <;> simp [h]
  · rintro (rfl | rfl)
    · exact ⟨XWord.step_left XWord.base XWord.base, by simp⟩
    · exact ⟨XWord.step_right XWord.base XWord.base, by simp⟩

lemma ncard_xN_two : (xN 2).ncard = a 1 := by
  have := xN_finite 2
  rw [xN_two, Set.ncard_pair (by simp), a_1]

lemma XWord.eq_of_length_three {w : Word} (hw : XWord w) (h : w.length = 3) :
    w = [-1, -2, 0] ∨ w = [-1, -1, 0] ∨ w = [-1, 0, 1] ∨
      w = [0, -1, 0] ∨ w = [0, 1, 0] ∨ w = [0, 1, 1] ∨ w = [0, 2, 1] :=
  match w, hw with
  | _, .base => by simp at h
  | _, @XWord.step_left u v hu hv => by
    have hsum : u.length + v.length = 3 := by
      simpa [l] using h
    have hsplit : u.length = 1 ∨ u.length = 2 := by
      have := hu.length_pos
      have := hv.length_pos
      omega
    rcases hsplit with hu1 | hu2
    · have hv2 : v.length = 2 := by omega
      have hu0 := XWord.eq_base_of_length_one hu hu1
      rcases XWord.eq_of_length_two hv hv2 with hv0 | hv0
      · subst u; subst v; simp [l]
      · subst u; subst v; simp [l]
    · have hv1 : v.length = 1 := by omega
      have hv0 := XWord.eq_base_of_length_one hv hv1
      rcases XWord.eq_of_length_two hu hu2 with hu0 | hu0
      · subst u; subst v; simp [l]
      · subst u; subst v; simp [l]
  | _, @XWord.step_right u v hu hv => by
    have hsum : u.length + v.length = 3 := by
      simpa [r] using h
    have hsplit : u.length = 1 ∨ u.length = 2 := by
      have := hu.length_pos
      have := hv.length_pos
      omega
    rcases hsplit with hu1 | hu2
    · have hv2 : v.length = 2 := by omega
      have hu0 := XWord.eq_base_of_length_one hu hu1
      rcases XWord.eq_of_length_two hv hv2 with hv0 | hv0
      · subst u; subst v; simp [r]
      · subst u; subst v; simp [r]
    · have hv1 : v.length = 1 := by omega
      have hv0 := XWord.eq_base_of_length_one hv hv1
      rcases XWord.eq_of_length_two hu hu2 with hu0 | hu0
      · subst u; subst v; simp [r]
      · subst u; subst v; simp [r]

def xN3Finset : Finset Word :=
  {[-1, -2, 0], [-1, -1, 0], [-1, 0, 1], [0, -1, 0], [0, 1, 0], [0, 1, 1],
    [0, 2, 1]}

lemma length_three_words : xN3Finset.card = 7 := by
  decide

lemma XWord.neg_one_neg_two_zero : XWord [-1, -2, 0] := by
  have h : l [-1, 0] ++ [0] = [-1, -2, 0] := by simp [l]
  have hu : XWord [-1, 0] := by
    simpa [l] using XWord.step_left XWord.base XWord.base
  exact h ▸ XWord.step_left hu XWord.base

lemma XWord.neg_one_neg_one_zero : XWord [-1, -1, 0] := by
  have h : l [0] ++ [-1, 0] = [-1, -1, 0] := by simp [l]
  have hv : XWord [-1, 0] := by
    simpa [l] using XWord.step_left XWord.base XWord.base
  exact h ▸ XWord.step_left XWord.base hv

lemma XWord.neg_one_zero_one : XWord [-1, 0, 1] := by
  have h : l [0] ++ [0, 1] = [-1, 0, 1] := by simp [l]
  have hv : XWord [0, 1] := by
    simpa [r] using XWord.step_right XWord.base XWord.base
  exact h ▸ XWord.step_left XWord.base hv

lemma XWord.zero_neg_one_zero : XWord [0, -1, 0] := by
  have h : l [0, 1] ++ [0] = [0, -1, 0] := by simp [l]
  have hu : XWord [0, 1] := by
    simpa [r] using XWord.step_right XWord.base XWord.base
  exact h ▸ XWord.step_left hu XWord.base

lemma XWord.zero_one_zero : XWord [0, 1, 0] := by
  have h : [0] ++ r [-1, 0] = [0, 1, 0] := by simp [r]
  have hv : XWord [-1, 0] := by
    simpa [l] using XWord.step_left XWord.base XWord.base
  exact h ▸ XWord.step_right XWord.base hv

lemma XWord.zero_one_one : XWord [0, 1, 1] := by
  have h : [0, 1] ++ r [0] = [0, 1, 1] := by simp [r]
  have hu : XWord [0, 1] := by
    simpa [r] using XWord.step_right XWord.base XWord.base
  exact h ▸ XWord.step_right hu XWord.base

lemma XWord.zero_two_one : XWord [0, 2, 1] := by
  have h : [0] ++ r [0, 1] = [0, 2, 1] := by simp [r]
  have hv : XWord [0, 1] := by
    simpa [r] using XWord.step_right XWord.base XWord.base
  exact h ▸ XWord.step_right XWord.base hv

lemma xN_three : xN 3 = ↑xN3Finset := by
  ext w
  constructor
  · intro hw
    rcases XWord.eq_of_length_three hw.1 hw.2 with
      h | h | h | h | h | h | h <;> simp [xN3Finset, h]
  · intro hw
    simp [xN3Finset] at hw
    rcases hw with h | h | h | h | h | h | h
    · exact ⟨h ▸ XWord.neg_one_neg_two_zero, by simp [h]⟩
    · exact ⟨h ▸ XWord.neg_one_neg_one_zero, by simp [h]⟩
    · exact ⟨h ▸ XWord.neg_one_zero_one, by simp [h]⟩
    · exact ⟨h ▸ XWord.zero_neg_one_zero, by simp [h]⟩
    · exact ⟨h ▸ XWord.zero_one_zero, by simp [h]⟩
    · exact ⟨h ▸ XWord.zero_one_one, by simp [h]⟩
    · exact ⟨h ▸ XWord.zero_two_one, by simp [h]⟩

lemma ncard_xN_three : (xN 3).ncard = a 2 := by
  have := xN_finite 3
  rw [xN_three, Set.ncard_coe_finset, length_three_words, a_2]

-- Right-irreducible words and right combs from `[0]`

/-- Words in `X` with no right parse. -/
def RIrreducible (w : Word) : Prop :=
  XWord w ∧ ∀ u v, ¬ IsRightParse w u v

/-- Smallest set containing `[0]` and closed under `u ++ r v` for `v ∈ X`. -/
inductive YWord : Word → Prop
  | base : YWord [0]
  | step {u v : Word} (hu : YWord u) (hv : XWord v) : YWord (u ++ r v)

lemma YWord.xWord {w : Word} (hw : YWord w) : XWord w :=
  match hw with
  | .base => XWord.base
  | .step hu hv => XWord.step_right (YWord.xWord hu) hv

lemma YWord.ne_nil {w : Word} (hw : YWord w) : w ≠ [] :=
  hw.xWord.ne_nil

/-- Central-binomial tail counts: `H 0 = 1` and `H (m+1) = C(2m+1, m)`. -/
def H : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1).choose m

lemma H_zero : H 0 = 1 := rfl

lemma H_one : H 1 = 1 := by
  simp [H]

lemma H_two : H 2 = 3 := by
  simp [H]

lemma H_three : H 3 = 10 := by
  decide

lemma H_succ_eq_mul_catalan (n : ℕ) :
    H (n + 1) = (2 * n + 1) * catalan n := by
  have hchoose :
      (2 * n).choose n * (2 * n + 1) = (2 * n + 1).choose n * (n + 1) := by
    have h := Nat.choose_mul_succ_eq (2 * n) n
    have hsub : 2 * n + 1 - n = n + 1 := by omega
    simpa [hsub] using h
  have hc := succ_mul_catalan_eq_centralBinom n
  refine Nat.mul_left_cancel (Nat.succ_pos n) ?_
  calc
    (n + 1) * H (n + 1) = (n + 1) * (2 * n + 1).choose n := rfl
    _ = (2 * n).choose n * (2 * n + 1) := by
      rw [Nat.mul_comm (n + 1), hchoose]
    _ = (2 * n + 1) * Nat.centralBinom n := by
      rw [Nat.centralBinom, Nat.mul_comm]
    _ = (2 * n + 1) * ((n + 1) * catalan n) := by
      rw [hc]
    _ = (n + 1) * ((2 * n + 1) * catalan n) := by
      ring

lemma two_mul_H_succ (n : ℕ) :
    2 * H (n + 1) = Nat.centralBinom (n + 1) := by
  have hsym := Nat.choose_symm_half n
  have hs : (2 * n + 2).choose (n + 1) = 2 * (2 * n + 1).choose n := by
    have hsucc : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [hsucc, Nat.choose_succ_succ, hsym]
    ring
  have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
  simp only [H, Nat.centralBinom, h2]
  exact hs.symm

lemma two_mul_H {n : ℕ} (hn : 1 ≤ n) : 2 * H n = Nat.centralBinom n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  exact two_mul_H_succ m

lemma H_eq_mul_catalan {n : ℕ} (hn : 1 ≤ n) :
    H n = (2 * (n - 1) + 1) * catalan (n - 1) := by
  convert H_succ_eq_mul_catalan (n - 1)
  exact (Nat.sub_add_cancel hn).symm

lemma sum_range_sub_eq (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.range (n + 1), f (n - k) =
      ∑ k ∈ Finset.range (n + 1), f k := by
  refine Finset.sum_nbij' (fun k => n - k) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have : k < n + 1 := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    have : k < n + 1 := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    have : k < n + 1 := Finset.mem_range.mp hk
    omega
  · intro k hk
    have : k < n + 1 := Finset.mem_range.mp hk
    omega
  · intro k hk
    have : k < n + 1 := Finset.mem_range.mp hk
    omega

lemma nat_mul_sum (a : ℕ) (s : Finset ℕ) (f : ℕ → ℕ) :
    a * ∑ k ∈ s, f k = ∑ k ∈ s, a * f k := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x s hx ih
    rw [Finset.sum_insert hx, Finset.sum_insert hx, mul_add, ih]

lemma two_mul_sum_weighted_catalan (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), k * catalan k * catalan (n - k) =
      n * catalan (n + 1) := by
  have hsym :
      ∑ k ∈ Finset.range (n + 1), k * catalan k * catalan (n - k) =
        ∑ k ∈ Finset.range (n + 1),
          (n - k) * catalan k * catalan (n - k) := by
    have hr :=
      sum_range_sub_eq n (fun k => k * catalan k * catalan (n - k))
    trans ∑ k ∈ Finset.range (n + 1),
        (n - k) * catalan (n - k) * catalan k
    · refine hr.symm.trans ?_
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : n - (n - k) = k := Nat.sub_sub_self hk'
      rw [this]
    · refine Finset.sum_congr rfl ?_
      intro k _hk
      ac_rfl
  have hadd :
      ∑ k ∈ Finset.range (n + 1), k * catalan k * catalan (n - k) +
        ∑ k ∈ Finset.range (n + 1),
          (n - k) * catalan k * catalan (n - k) =
        ∑ k ∈ Finset.range (n + 1), n * catalan k * catalan (n - k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsplit :
        k * catalan k * catalan (n - k) +
          (n - k) * catalan k * catalan (n - k) =
          (k + (n - k)) * catalan k * catalan (n - k) := by
      ring
    rw [hsplit, Nat.add_sub_of_le hk']
  have hcat :
      ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) =
        catalan (n + 1) := by
    rw [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => catalan x * catalan y)]
  have h2 :
      2 * ∑ k ∈ Finset.range (n + 1), k * catalan k * catalan (n - k) =
        ∑ k ∈ Finset.range (n + 1), n * catalan k * catalan (n - k) := by
    rw [← hsym] at hadd
    linarith
  have hfactor :
      ∑ k ∈ Finset.range (n + 1), n * catalan k * catalan (n - k) =
        n * ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) := by
    have hassoc :
        ∑ k ∈ Finset.range (n + 1), n * catalan k * catalan (n - k) =
          ∑ k ∈ Finset.range (n + 1), n * (catalan k * catalan (n - k)) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      ring
    rw [hassoc]
    exact (nat_mul_sum n (Finset.range (n + 1))
      (fun k => catalan k * catalan (n - k))).symm
  rw [h2, hfactor, hcat]

lemma sum_odd_mul_catalan (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (2 * k + 1) * catalan k * catalan (n - k) =
      (n + 1) * catalan (n + 1) := by
  have hcat :
      ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) =
        catalan (n + 1) := by
    rw [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => catalan x * catalan y)]
  have hodd :
      ∑ k ∈ Finset.range (n + 1), (2 * k + 1) * catalan k * catalan (n - k) =
        2 * ∑ k ∈ Finset.range (n + 1), k * catalan k * catalan (n - k) +
          ∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    ring
  rw [hodd, two_mul_sum_weighted_catalan, hcat]
  ring

lemma sum_H_mul_catalan_succ :
    ∀ n, ∑ j ∈ Finset.range (n + 1), H j * catalan (n + 1 - j) = H (n + 1)
  | 0 => by
    simp [H_zero, H_one, catalan_one]
  | n + 1 => by
    have hsplit :
        ∑ j ∈ Finset.range (n + 2), H j * catalan (n + 2 - j) =
          catalan (n + 2) +
            ∑ j ∈ Finset.Icc 1 (n + 1), H j * catalan (n + 2 - j) := by
      have hrange :
          Finset.range (n + 2) = insert 0 (Finset.Icc 1 (n + 1)) := by
        ext k
        simp [Finset.mem_range, Finset.mem_Icc]
        omega
      rw [hrange, Finset.sum_insert]
      · simp [H_zero]
      · simp [Finset.mem_Icc]
    have hsum :
        ∑ j ∈ Finset.Icc 1 (n + 1), H j * catalan (n + 2 - j) =
          ∑ k ∈ Finset.range (n + 1),
            (2 * k + 1) * catalan k * catalan (n + 1 - k) := by
      rw [Icc_one_eq_map_succ, Finset.sum_map]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      have hH : H (k + 1) = (2 * k + 1) * catalan k :=
        H_succ_eq_mul_catalan k
      have hidx : n + 2 - (k + 1) = n + 1 - k := by omega
      simp [Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, hH, hidx]
    have hodd := sum_odd_mul_catalan (n + 1)
    have hfull :
        ∑ k ∈ Finset.range (n + 2),
            (2 * k + 1) * catalan k * catalan (n + 1 - k) =
          (n + 2) * catalan (n + 2) := by
      simpa [Nat.succ_eq_add_one] using hodd
    have hdecomp := Finset.sum_range_succ
      (fun k => (2 * k + 1) * catalan k * catalan (n + 1 - k)) (n + 1)
    have hz : n + 1 - (n + 1) = 0 := by omega
    have hterm :
        (2 * (n + 1) + 1) * catalan (n + 1) * catalan (n + 1 - (n + 1)) =
          (2 * (n + 1) + 1) * catalan (n + 1) := by
      rw [hz, catalan_zero, mul_one]
    have hidx : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    have hsum_add :
        ∑ k ∈ Finset.range (n + 1),
            (2 * k + 1) * catalan k * catalan (n + 1 - k) +
          (2 * n + 3) * catalan (n + 1) =
          (n + 2) * catalan (n + 2) := by
      have hfull' := hfull
      rw [hdecomp, hterm, hidx] at hfull'
      exact hfull'
    have hL :
        catalan (n + 2) +
            ∑ k ∈ Finset.range (n + 1),
              (2 * k + 1) * catalan k * catalan (n + 1 - k) +
          (2 * n + 3) * catalan (n + 1) =
          (n + 3) * catalan (n + 2) := by
      rw [add_assoc, hsum_add]
      ring
    have hH : H (n + 2) = (2 * n + 3) * catalan (n + 1) := by
      have := H_succ_eq_mul_catalan (n + 1)
      have hn2 : n + 1 + 1 = n + 2 := by omega
      have hodd' : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      simpa [hn2, hodd'] using this
    have hR :
        H (n + 2) + (2 * n + 3) * catalan (n + 1) =
          (n + 3) * catalan (n + 2) := by
      have hcent := succ_mul_catalan_eq_centralBinom (n + 2)
      have htwo := two_mul_H_succ (n + 1)
      have hn2 : n + 1 + 1 = n + 2 := by omega
      have hcent' : (n + 3) * catalan (n + 2) = Nat.centralBinom (n + 2) := by
        simpa [Nat.succ_eq_add_one] using hcent
      have htwo' : 2 * H (n + 2) = Nat.centralBinom (n + 2) := by
        simpa [hn2] using htwo
      rw [hH]
      linarith [hcent', htwo']
    have hcancel := Nat.add_right_cancel (hL.trans hR.symm)
    rw [hsplit, hsum]
    exact hcancel

lemma sum_H_mul_catalan {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, H j * catalan (n - j) = H n := by
  have h := sum_H_mul_catalan_succ (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  exact h

lemma RIrreducible.xWord {w : Word} (h : RIrreducible w) : XWord w := h.1

lemma RIrreducible.getLast_ne_one {w : Word} (h : RIrreducible w) :
    w.getLast h.xWord.ne_nil ≠ 1 := by
  intro hlast
  obtain ⟨u, v, hp⟩ := exists_right_parse_of_getLast_eq_one h.xWord hlast
  exact h.2 u v hp

lemma RIrreducible.getLast_eq_zero {w : Word} (h : RIrreducible w) :
    w.getLast h.xWord.ne_nil = 0 := by
  have := h.xWord.getLast_mem
  rcases this with h0 | h1
  · exact h0
  · exact (h.getLast_ne_one h1).elim

lemma YWord.head_eq_zero {w : Word} (hw : YWord w) :
    w.head hw.ne_nil = 0 :=
  match w, hw with
  | _, .base => by simp
  | _, @YWord.step u v hu hv => by
    have : (u ++ r v).head (YWord.ne_nil (YWord.step hu hv)) =
        u.head hu.xWord.ne_nil :=
      head_append_of_ne_nil hu.xWord.ne_nil
    rw [this]
    exact YWord.head_eq_zero hu

lemma XWord.yWord_of_pword_head_zero {w : Word} (hw : XWord w) (hc : w.count 0 = 1)
    (hhead : w.head hw.ne_nil = 0) : YWord w :=
  match w, hw with
  | _, .base => YWord.base
  | _, @XWord.step_left u v hu hv => by
    have hp : PWord (l u ++ v) := ⟨XWord.step_left hu hv, hc⟩
    have hones := (PWord.of_step_left hu hv hp).2
    have h1u : (1 : ℤ) ∉ u := by simpa [count_eq_zero] using hones
    have hu_ne := hu.ne_nil
    have hhd : (l u ++ v).head (XWord.ne_nil (XWord.step_left hu hv)) =
        (l u).head (l_ne_nil hu_ne) :=
      head_append_of_ne_nil (l_ne_nil hu_ne)
    have hlast1 : u.getLast hu_ne = 1 := by
      have : u.getLast hu_ne - 1 = 0 := by
        rw [← head_l hu_ne, ← hhd, hhead]
      omega
    exact (h1u (by simpa [hlast1] using List.getLast_mem hu_ne)).elim
  | _, @XWord.step_right u v hu hv => by
    have hp : PWord (u ++ r v) := ⟨XWord.step_right hu hv, hc⟩
    have huP := (PWord.of_step_right hu hv hp).1
    have hu_ne := hu.ne_nil
    have hhead_u : u.head hu_ne = 0 := by
      have : (u ++ r v).head (XWord.ne_nil (XWord.step_right hu hv)) =
          u.head hu_ne :=
        head_append_of_ne_nil hu_ne
      exact this ▸ hhead
    exact YWord.step (XWord.yWord_of_pword_head_zero hu huP.2 hhead_u) hv

lemma PWord.yWord_of_head_eq_zero {w : Word} (hw : PWord w)
    (hhead : w.head hw.1.ne_nil = 0) : YWord w :=
  XWord.yWord_of_pword_head_zero hw.1 hw.2 hhead

/-- Concatenating an arbitrary Xia word with the tail of a `YWord` stays in `X`.
This is the easy half of the experimental rebuild map. -/
lemma XWord.append_YWord_tail {c y : Word} (hc : XWord c) (hy : YWord y) :
    XWord (c ++ y.tail) :=
  match y, hy with
  | _, .base => by
    simpa using hc
  | _, @YWord.step u v hu hv => by
    have hu_ne := hu.ne_nil
    have : (u ++ r v).tail = u.tail ++ r v := tail_append_of_ne_nil hu_ne
    rw [this, ← append_assoc]
    exact XWord.step_right (XWord.append_YWord_tail hc hu) hv

lemma PWord.append_tail_of_head_eq_zero {p q : Word} (hp : PWord p) (hq : PWord q)
    (hhead : q.head hq.1.ne_nil = 0) : PWord (p ++ q.tail) := by
  have hy := PWord.yWord_of_head_eq_zero hq hhead
  have hx := XWord.append_YWord_tail hp.1 hy
  have hqeq : q = 0 :: q.tail := by
    have h := (cons_head_tail hq.1.ne_nil).symm
    simpa [hhead] using h
  have htail0 : q.tail.count 0 = 0 := by
    have hcount := hq.2
    rw [hqeq, count_cons_self] at hcount
    omega
  have hcount : (p ++ q.tail).count 0 = 1 := by
    simp [count_append, hp.2, htail0]
  exact ⟨hx, hcount⟩

lemma take_append_getLast {w : Word} (h : w ≠ []) :
    w.take (w.length - 1) ++ [w.getLast h] = w := by
  have hpos : 0 < w.length := length_pos_iff.mpr h
  have hlt : w.length - 1 < w.length := by omega
  have hlen : w.length - 1 + 1 = w.length := by omega
  have hlast : w.getLast h = w[w.length - 1]'(hlt) := getLast_eq_getElem h
  calc
    w.take (w.length - 1) ++ [w.getLast h]
        = w.take (w.length - 1) ++ [w[w.length - 1]'(hlt)] := by rw [hlast]
    _ = w.take (w.length - 1 + 1) := (take_succ_eq_append_getElem hlt).symm
    _ = w.take w.length := by rw [hlen]
    _ = w := by simp

lemma PWord.idxOf_of_getLast_eq_zero {w : Word} (hw : PWord w)
    (hlast : w.getLast hw.1.ne_nil = 0) : w.idxOf 0 = w.length - 1 := by
  have hlt := hw.idxOf_lt_length
  have hle : w.idxOf 0 ≤ w.length - 1 := by omega
  refine Nat.le_antisymm hle ?_
  by_contra hne
  have hidx : w.idxOf 0 < w.length - 1 := Nat.lt_of_not_ge hne
  have htake : (0 : ℤ) ∈ w.take (w.length - 1) :=
    (mem_take_iff_idxOf_lt hw.1.zero_mem).mpr (by omega)
  have hsplit := take_append_getLast hw.1.ne_nil
  have hcount : w.count 0 = (w.take (w.length - 1)).count 0 + 1 := by
    rw [← hsplit, count_append, hlast]
    simp
  have : 0 < (w.take (w.length - 1)).count 0 := count_pos_iff.mpr htake
  have := hw.2
  omega

lemma RightWord.idxOf_eq_zero {w : Word} (hw : RightWord w) : w.idxOf 0 = 0 :=
  (idxOf_eq_zero_iff_head_eq hw.xWord.ne_nil).mpr hw.head_eq_zero

lemma RightWord.idxOf_rho {w : Word} (hw : RightWord w) :
    (rho w).idxOf 0 = w.length - 1 := by
  have hρ := PWord.rho hw.pWord
  have hlast : (rho w).getLast (rho_ne_nil hw.xWord.ne_nil) = 0 := by
    rw [rho_getLast hw.xWord.ne_nil, hw.head_eq_zero]
    simp
  have hidx := PWord.idxOf_of_getLast_eq_zero hρ hlast
  simpa [length_rho] using hidx

lemma RightWord.count_zero_tail {v : Word} (hv : RightWord v) : v.tail.count 0 = 0 := by
  have hqeq : v = 0 :: v.tail := by
    have h := (cons_head_tail hv.xWord.ne_nil).symm
    simpa [hv.head_eq_zero] using h
  have hcount := hv.pWord.2
  rw [hqeq, count_cons_self] at hcount
  omega

lemma RightWord.not_mem_zero_tail {v : Word} (hv : RightWord v) : (0 : ℤ) ∉ v.tail :=
  count_eq_zero.mp (RightWord.count_zero_tail hv)

def pwordLeft (w : Word) : Word :=
  rho (w.take (w.idxOf 0) ++ [0])

def pwordRight (w : Word) : Word :=
  0 :: w.drop (w.idxOf 0 + 1)

lemma pwordLeft_rightWord {w : Word} (hw : PWord w) :
    RightWord (pwordLeft w) := by
  have hp := PWord.take_idxOf_concat_zero hw
  have hρ := PWord.rho hp
  have hne : w.take (w.idxOf 0) ++ [0] ≠ [] := by simp
  have hlast : (w.take (w.idxOf 0) ++ [0]).getLast hne = 0 :=
    getLast_append_singleton _
  have hhead : (rho (w.take (w.idxOf 0) ++ [0])).head (rho_ne_nil hne) = 0 := by
    rw [rho_head hne, hlast]
    simp
  exact RightWord.of_head_eq_zero hρ hhead

lemma pwordRight_rightWord {w : Word} (hw : PWord w) :
    RightWord (pwordRight w) :=
  RightWord.of_head_eq_zero (PWord.cons_zero_drop_succ_idxOf hw)
    (by simp [pwordRight])

lemma length_pwordLeft {w : Word} (hw : PWord w) :
    (pwordLeft w).length = w.idxOf 0 + 1 := by
  have hlt := hw.idxOf_lt_length
  simp [pwordLeft, length_rho, length_take]
  omega

lemma length_pwordRight {w : Word} (hw : PWord w) :
    (pwordRight w).length = w.length - w.idxOf 0 := by
  have hlt := hw.idxOf_lt_length
  simp [pwordRight]
  omega

lemma pwordLeft_mem_rightN {w : Word} (hw : PWord w) :
    pwordLeft w ∈ rightN (w.idxOf 0 + 1) :=
  ⟨pwordLeft_rightWord hw, length_pwordLeft hw⟩

lemma pwordRight_mem_rightN {w : Word} (hw : PWord w) :
    pwordRight w ∈ rightN (w.length - w.idxOf 0) :=
  ⟨pwordRight_rightWord hw, length_pwordRight hw⟩

def glueP (u v : Word) : Word :=
  rho u ++ v.tail

lemma glueP_pWord {u v : Word} (hu : RightWord u) (hv : RightWord v) :
    PWord (glueP u v) :=
  PWord.append_tail_of_head_eq_zero (PWord.rho hu.pWord) hv.pWord hv.head_eq_zero

lemma glueP_length {u v : Word} (_hu : RightWord u) (hv : RightWord v) :
    (glueP u v).length = u.length + v.length - 1 := by
  have := hv.xWord.length_pos
  simp [glueP, length_rho, length_tail]
  omega

lemma glueP_idxOf {u v : Word} (hu : RightWord u) (_hv : RightWord v) :
    (glueP u v).idxOf 0 = u.length - 1 := by
  have h0u : (0 : ℤ) ∈ rho u := (PWord.rho hu.pWord).1.zero_mem
  rw [glueP, idxOf_append_of_mem h0u, RightWord.idxOf_rho hu]

lemma glueP_leftRight {u v : Word} (hu : RightWord u) (hv : RightWord v) :
    pwordLeft (glueP u v) = u := by
  have hidx := glueP_idxOf hu hv
  have hu_pos := hu.xWord.length_pos
  have hle : u.length - 1 ≤ (rho u).length := by
    simp [length_rho]
  have htake : (glueP u v).take ((glueP u v).idxOf 0) = (rho u).take (u.length - 1) := by
    unfold glueP at hidx ⊢
    rw [hidx, take_append_of_le_length hle]
  have hlast : (rho u).getLast (rho_ne_nil hu.xWord.ne_nil) = 0 := by
    rw [rho_getLast hu.xWord.ne_nil, hu.head_eq_zero]
    simp
  have hrec : (rho u).take (u.length - 1) ++ [0] = rho u := by
    have h := take_append_getLast (rho_ne_nil hu.xWord.ne_nil)
    rw [length_rho, hlast] at h
    exact h
  rw [pwordLeft, htake, hrec, rho_rho]

lemma glueP_rightRight {u v : Word} (hu : RightWord u) (hv : RightWord v) :
    pwordRight (glueP u v) = v := by
  have hu_pos := hu.xWord.length_pos
  have hidx := glueP_idxOf hu hv
  have hidx1 : (glueP u v).idxOf 0 + 1 = u.length := by omega
  have hdrop : (glueP u v).drop ((glueP u v).idxOf 0 + 1) = v.tail := by
    have hlenρ : (rho u).length = u.length := length_rho u
    unfold glueP at hidx1 ⊢
    rw [hidx1, ← hlenρ, drop_left]
  have hv0 : v = 0 :: v.tail := by
    have h := (cons_head_tail hv.xWord.ne_nil).symm
    simpa [hv.head_eq_zero] using h
  rw [pwordRight, hdrop]
  exact hv0.symm

lemma glueP_of_leftRight_rightRight {w : Word} (hw : PWord w) :
    glueP (pwordLeft w) (pwordRight w) = w := by
  rw [glueP, pwordLeft, pwordRight, rho_rho, tail_cons]
  exact PWord.take_idxOf_concat_zero_append_drop hw

def pN (n : ℕ) : Set Word :=
  {w | PWord w ∧ w.length = n}

lemma pN_subset_xN (n : ℕ) : pN n ⊆ xN n :=
  fun _ hw => ⟨hw.1.1, hw.2⟩

lemma pN_finite (n : ℕ) : (pN n).Finite :=
  (xN_finite n).subset (pN_subset_xN n)

noncomputable def pNFinset (n : ℕ) : Finset Word :=
  (pN_finite n).toFinset

lemma mem_pNFinset {n : ℕ} {w : Word} : w ∈ pNFinset n ↔ w ∈ pN n :=
  Set.Finite.mem_toFinset (pN_finite n)

lemma ncard_pN_eq_card (n : ℕ) : (pN n).ncard = (pNFinset n).card :=
  Set.ncard_eq_toFinset_card _ (pN_finite n)

lemma disjoint_rightNFinset_product_succ {i j k l : ℕ} (hij : i ≠ j) :
    Disjoint (rightNFinset (i + 1) ×ˢ rightNFinset k)
      (rightNFinset (j + 1) ×ˢ rightNFinset l) :=
  disjoint_rightNFinset_product (by omega)

noncomputable def pNPairs (n : ℕ) : Finset (Word × Word) :=
  (Finset.range n).biUnion fun k =>
    rightNFinset (k + 1) ×ˢ rightNFinset (n - k)

lemma mem_pNPairs {n : ℕ} {p : Word × Word} :
    p ∈ pNPairs n ↔
      ∃ k ∈ Finset.range n, p.1 ∈ rightN (k + 1) ∧ p.2 ∈ rightN (n - k) := by
  simp [pNPairs, Finset.mem_biUnion, Finset.mem_product, mem_rightNFinset]

lemma card_pNPairs (n : ℕ) :
    (pNPairs n).card =
      ∑ k ∈ Finset.range n,
        (rightNFinset (k + 1)).card * (rightNFinset (n - k)).card := by
  have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint
      (fun k => rightNFinset (k + 1) ×ˢ rightNFinset (n - k)) := by
    intro i _ j _ hij
    exact disjoint_rightNFinset_product_succ hij
  rw [pNPairs, Finset.card_biUnion hdisj]
  simp [Finset.card_product]

lemma injOn_glueP_pNPairs (n : ℕ) :
    Set.InjOn (fun p : Word × Word => glueP p.1 p.2) (pNPairs n) := by
  intro p hp q hq heq
  obtain ⟨k, _, hu, hv⟩ := mem_pNPairs.mp hp
  obtain ⟨k', _, hu', hv'⟩ := mem_pNPairs.mp hq
  have hp1 : p.1 = q.1 := by
    have := congrArg pwordLeft heq
    simpa [glueP_leftRight hu.1 hv.1, glueP_leftRight hu'.1 hv'.1] using this
  have hp2 : p.2 = q.2 := by
    have := congrArg pwordRight heq
    simpa [glueP_rightRight hu.1 hv.1, glueP_rightRight hu'.1 hv'.1] using this
  exact Prod.ext hp1 hp2

lemma image_pNPairs (n : ℕ) (hn : 1 ≤ n) :
    (pNPairs n).image (fun p => glueP p.1 p.2) = pNFinset n := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, hk, hu, hv⟩ := mem_pNPairs.mp hp
    have hwP := glueP_pWord hu.1 hv.1
    have hlen : (glueP p.1 p.2).length = n := by
      have hk' : k < n := Finset.mem_range.mp hk
      have := glueP_length hu.1 hv.1
      have h1 := hu.2
      have h2 := hv.2
      omega
    exact mem_pNFinset.mpr ⟨hwP, hlen⟩
  · intro hw
    have hw' := mem_pNFinset.mp hw
    have hlenw : w.length = n := hw'.2
    let k := w.idxOf 0
    have hk : k ∈ Finset.range n := by
      have := hw'.1.idxOf_lt_length
      simp [Finset.mem_range, k]
      omega
    have hu := pwordLeft_mem_rightN hw'.1
    have hv := pwordRight_mem_rightN hw'.1
    have hvN : pwordRight w ∈ rightN (n - k) := by
      have := length_pwordRight hw'.1
      simpa [k, hlenw] using hv
    have huN : pwordLeft w ∈ rightN (k + 1) := by
      simpa [k] using hu
    refine Finset.mem_image.mpr ⟨(pwordLeft w, pwordRight w), ?_, ?_⟩
    · exact mem_pNPairs.mpr ⟨k, hk, huN, hvN⟩
    · exact glueP_of_leftRight_rightRight hw'.1

lemma ncard_pN_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    (pN n).ncard =
      ∑ k ∈ Finset.range n, (rightN (k + 1)).ncard * (rightN (n - k)).ncard := by
  have himg := image_pNPairs n hn
  have hinj := injOn_glueP_pNPairs n
  have hcard : (pNFinset n).card = (pNPairs n).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  rw [ncard_pN_eq_card, hcard, card_pNPairs]
  simp [ncard_rightN_eq_card]

lemma ncard_pN_eq_catalan {n : ℕ} (hn : 1 ≤ n) :
    (pN n).ncard = catalan n := by
  rw [ncard_pN_eq_sum n hn]
  have hsum :
      ∑ k ∈ Finset.range n, (rightN (k + 1)).ncard * (rightN (n - k)).ncard =
        ∑ k ∈ Finset.range n, catalan k * catalan (n - 1 - k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have h1 : (rightN (k + 1)).ncard = catalan k := ncard_rightN_succ_eq_catalan k
    have h2 : (rightN (n - k)).ncard = catalan (n - k - 1) :=
      ncard_rightN_eq_catalan (by omega)
    have hidx : n - k - 1 = n - 1 - k := by omega
    rw [h1, h2, hidx]
  rw [hsum]
  have hn' : n = n - 1 + 1 := by omega
  rw [show catalan n = catalan (n - 1 + 1) from congrArg catalan hn',
    catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => catalan x * catalan y)]
  have hsucc : (n - 1).succ = n := by
    rw [Nat.succ_eq_add_one]
    exact hn'.symm
  rw [hsucc]

lemma YWord.exists_right_parse_of_length_ge_two {w : Word} (hw : YWord w)
    (hlen : 2 ≤ w.length) : ∃ u v, IsRightParse w u v :=
  match w, hw with
  | _, .base => by
    simp at hlen
  | _, @YWord.step u v hu hv =>
    ⟨u, v, hu.xWord, hv, rfl⟩

lemma YWord.shortest_remainder_is_pword {w : Word} (hw : YWord w)
    (hlen : 2 ≤ w.length) :
    ∃ u v, IsRightParse w u v ∧ PWord v ∧
      ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length := by
  obtain ⟨u, v, hp, hmin⟩ :=
    exists_shortest_right_parse (YWord.exists_right_parse_of_length_ge_two hw hlen)
  exact ⟨u, v, hp, XWord.of_isRightParse_shortest hp hmin, hmin⟩

lemma yword_shortest_left_of_repr :
    ∀ n u0 v0, v0.length = n → YWord u0 → XWord v0 →
      ∀ u p, IsRightParse (u0 ++ r v0) u p →
        (∀ u2 v2, IsRightParse (u0 ++ r v0) u2 v2 → p.length ≤ v2.length) →
        YWord u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u0 v0 hlen hu0 hv0 u p hp hmin
    by_cases hP : v0.count 0 = 1
    · have hvP : PWord v0 := ⟨hv0, hP⟩
      have hp0 : IsRightParse (u0 ++ r v0) u0 v0 := ⟨hu0.xWord, hv0, rfl⟩
      have hge := PWord.le_length_of_isRightParse_append_r hu0.xWord hvP hp
      have hle := hmin u0 v0 hp0
      have hplen : p.length = v0.length := Nat.le_antisymm hle hge
      have hulen : u.length = u0.length := by
        have := hp.length_add
        have := hp0.length_add
        omega
      have heq := eq_of_right_parse_eq (hp.2.2.symm.trans hp0.2.2) hulen
      exact heq.1 ▸ hu0
    · have hc : 2 ≤ v0.count 0 := by
        have := hv0.count_zero_pos
        omega
      obtain ⟨k, hk0, hkl, htk, hdk⟩ := XWord.exists_concat_split hv0 hc
      have hp0 : IsRightParse (u0 ++ r v0) u0 v0 := ⟨hu0.xWord, hv0, rfl⟩
      have hparse' : IsRightParse (u0 ++ r v0) (u0 ++ r (v0.drop k)) (v0.take k) :=
        IsRightParse.of_concat_remainder hp0 htk hdk (take_append_drop k v0).symm
      have hu1 : YWord (u0 ++ r (v0.drop k)) := YWord.step hu0 hdk
      have htklen : (v0.take k).length = k := by
        simp [length_take]
        omega
      have hlt : (v0.take k).length < n := by
        omega
      have hw_eq : u0 ++ r v0 = (u0 ++ r (v0.drop k)) ++ r (v0.take k) :=
        hparse'.2.2
      rw [hw_eq] at hp hmin
      exact ih (v0.take k).length hlt (u0 ++ r (v0.drop k)) (v0.take k)
        rfl hu1 htk u p hp hmin

lemma YWord.shortest_left_is_yword {w u v : Word} (hw : YWord w)
    (h : IsRightParse w u v)
    (hmin : ∀ u2 v2, IsRightParse w u2 v2 → v.length ≤ v2.length) :
    YWord u :=
  match w, hw with
  | _, .base => by
    have hsum := h.length_add
    have h1 : ([0] : Word).length = 1 := by simp
    have := h.pos_left
    have := h.pos_right
    omega
  | _, @YWord.step u0 v0 hu0 hv0 =>
    yword_shortest_left_of_repr v0.length u0 v0 rfl hu0 hv0 u v h hmin

def yN (n : ℕ) : Set Word :=
  {w | YWord w ∧ w.length = n}

lemma yN_subset_xN (n : ℕ) : yN n ⊆ xN n :=
  fun _ hw => ⟨hw.1.xWord, hw.2⟩

lemma yN_finite (n : ℕ) : (yN n).Finite :=
  (xN_finite n).subset (yN_subset_xN n)

noncomputable def yNFinset (n : ℕ) : Finset Word :=
  (yN_finite n).toFinset

lemma mem_yNFinset {n : ℕ} {w : Word} :
    w ∈ yNFinset n ↔ w ∈ yN n :=
  Set.Finite.mem_toFinset (yN_finite n)

lemma ncard_yN_eq_card (n : ℕ) :
    (yN n).ncard = (yNFinset n).card :=
  Set.ncard_eq_toFinset_card _ (yN_finite n)

lemma YWord.eq_base_of_length_one {w : Word} (hw : YWord w) (h : w.length = 1) :
    w = [0] :=
  XWord.eq_base_of_length_one hw.xWord h

lemma yN_one : yN 1 = {[0]} := by
  ext w
  constructor
  · intro hw
    have : w = [0] := YWord.eq_base_of_length_one hw.1 hw.2
    simp [this]
  · intro hw
    simp at hw
    subst hw
    exact ⟨YWord.base, by simp⟩

lemma ncard_yN_one : (yN 1).ncard = H 0 := by
  have := yN_finite 1
  rw [yN_one, Set.ncard_singleton, H_zero]

lemma disjoint_yNFinset_product {i j k l : ℕ} (hij : i ≠ j) :
    Disjoint (yNFinset i ×ˢ pNFinset k) (yNFinset j ×ˢ pNFinset l) := by
  refine Finset.disjoint_iff_ne.mpr ?_
  intro p hp q hq hpeq
  have hi : p.1.length = i := (mem_yNFinset.mp (Finset.mem_product.mp hp).1).2
  have hj : q.1.length = j := (mem_yNFinset.mp (Finset.mem_product.mp hq).1).2
  have : p.1.length = q.1.length := congrArg List.length (congrArg Prod.fst hpeq)
  omega

noncomputable def yNPairs (n : ℕ) : Finset (Word × Word) :=
  (Finset.Icc 1 (n - 1)).biUnion fun i =>
    yNFinset i ×ˢ pNFinset (n - i)

lemma mem_yNPairs {n : ℕ} {p : Word × Word} :
    p ∈ yNPairs n ↔
      ∃ i ∈ Finset.Icc 1 (n - 1), p.1 ∈ yN i ∧ p.2 ∈ pN (n - i) := by
  simp [yNPairs, Finset.mem_biUnion, Finset.mem_product, mem_yNFinset, mem_pNFinset]

lemma card_yNPairs (n : ℕ) :
    (yNPairs n).card =
      ∑ i ∈ Finset.Icc 1 (n - 1),
        (yNFinset i).card * (pNFinset (n - i)).card := by
  have hdisj : (Finset.Icc 1 (n - 1) : Set ℕ).PairwiseDisjoint
      (fun i => yNFinset i ×ˢ pNFinset (n - i)) := by
    intro i _ j _ hij
    exact disjoint_yNFinset_product hij
  rw [yNPairs, Finset.card_biUnion hdisj]
  simp [Finset.card_product]

lemma injOn_append_r_yNPairs (n : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1 ++ r p.2) (yNPairs n) := by
  intro p hp q hq heq
  obtain ⟨i, _, hu, hv⟩ := mem_yNPairs.mp hp
  obtain ⟨j, _, hu', hv'⟩ := mem_yNPairs.mp hq
  have hpP : IsRightParse (p.1 ++ r p.2) p.1 p.2 :=
    ⟨hu.1.xWord, hv.1.1, rfl⟩
  have hqP : IsRightParse (p.1 ++ r p.2) q.1 q.2 :=
    ⟨hu'.1.xWord, hv'.1.1, heq⟩
  have hminp : ∀ u2 v2, IsRightParse (p.1 ++ r p.2) u2 v2 →
      p.2.length ≤ v2.length :=
    fun u2 v2 h => PWord.le_length_of_isRightParse_append_r hu.1.xWord hv.1 h
  have hminq : ∀ u2 v2, IsRightParse (p.1 ++ r p.2) u2 v2 →
      q.2.length ≤ v2.length := by
    intro u2 v2 h
    have h' : IsRightParse (q.1 ++ r q.2) u2 v2 := by
      simpa [heq] using h
    exact PWord.le_length_of_isRightParse_append_r hu'.1.xWord hv'.1 h'
  obtain ⟨h1, h2⟩ := shortest_right_parse_unique hpP hqP hminp hminq
  exact Prod.ext h1 h2

lemma image_yNPairs (n : ℕ) (hn : 2 ≤ n) :
    (yNPairs n).image (fun p => p.1 ++ r p.2) = yNFinset n := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, hi, hu, hv⟩ := mem_yNPairs.mp hp
    have hwY : YWord (p.1 ++ r p.2) := YWord.step hu.1 hv.1.1
    have hlen : (p.1 ++ r p.2).length = n := by
      have hi1 := Finset.mem_Icc.mp hi
      rw [length_append_r, hu.2, hv.2]
      omega
    exact mem_yNFinset.mpr ⟨hwY, hlen⟩
  · intro hw
    have hw' := mem_yNFinset.mp hw
    have hlenw : w.length = n := hw'.2
    have hlen2 : 2 ≤ w.length := by omega
    obtain ⟨u, v, hp, hvP, hmin⟩ :=
      YWord.shortest_remainder_is_pword hw'.1 hlen2
    have huY := YWord.shortest_left_is_yword hw'.1 hp hmin
    have hsum := hp.length_add
    have hu_pos := huY.xWord.length_pos
    have hv_pos := hvP.1.length_pos
    have hi : u.length ∈ Finset.Icc 1 (n - 1) := by
      simp [Finset.mem_Icc]
      omega
    have huN : u ∈ yN u.length := ⟨huY, rfl⟩
    have hvN : v ∈ pN (n - u.length) := ⟨hvP, by omega⟩
    refine Finset.mem_image.mpr ⟨(u, v), ?_, hp.2.2.symm⟩
    exact mem_yNPairs.mpr ⟨u.length, hi, huN, hvN⟩

lemma ncard_yN_ge_two (n : ℕ) (hn : 2 ≤ n) :
    (yN n).ncard =
      ∑ i ∈ Finset.Icc 1 (n - 1), (yN i).ncard * (pN (n - i)).ncard := by
  have himg := image_yNPairs n hn
  have hinj := injOn_append_r_yNPairs n
  have hcard : (yNFinset n).card = (yNPairs n).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  rw [ncard_yN_eq_card, hcard, card_yNPairs]
  simp [ncard_yN_eq_card, ncard_pN_eq_card]

lemma ncard_yN_eq_H :
    ∀ n, (yN (n + 1)).ncard = H n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ncard_yN_one
    | succ n =>
      have h2 : 2 ≤ n + 2 := by omega
      have hidx : n + 2 - 1 = n + 1 := by omega
      rw [ncard_yN_ge_two (n + 2) h2, hidx]
      have hsum :
          ∑ i ∈ Finset.Icc 1 (n + 1),
              (yN i).ncard * (pN (n + 2 - i)).ncard =
            ∑ i ∈ Finset.Icc 1 (n + 1), H (i - 1) * catalan (n + 2 - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hile : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
        have hY : (yN i).ncard = H (i - 1) := by
          have hlt : i - 1 < n + 1 := by omega
          convert ih (i - 1) hlt
          exact (Nat.sub_add_cancel hi1).symm
        have hP : (pN (n + 2 - i)).ncard = catalan (n + 2 - i) := by
          have hpos : 1 ≤ n + 2 - i := by omega
          exact ncard_pN_eq_catalan hpos
        rw [hY, hP]
      rw [hsum, Icc_one_eq_map_succ, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
      have hfun : ∀ k ∈ Finset.range (n + 1),
          H (k + 1 - 1) * catalan (n + 2 - (k + 1)) =
            H k * catalan (n + 1 - k) := by
        intro k hk
        have : k < n + 1 := Finset.mem_range.mp hk
        have h1 : k + 1 - 1 = k := by omega
        have h2 : n + 2 - (k + 1) = n + 1 - k := by omega
        simp [h1, h2]
      rw [Finset.sum_congr rfl hfun, sum_H_mul_catalan_succ n]

lemma ncard_yN_eq_H_of_pos {n : ℕ} (hn : 1 ≤ n) :
    (yN n).ncard = H (n - 1) := by
  convert ncard_yN_eq_H (n - 1)
  exact (Nat.sub_add_cancel hn).symm

lemma exists_right_parse_append_YWord_tail {c y : Word} (hc : XWord c)
    (hy : YWord y) (hlen : 2 ≤ y.length) :
    ∃ u v, IsRightParse (c ++ y.tail) u v :=
  match y, hy with
  | _, .base => by
    simp at hlen
  | _, @YWord.step u v hu hv => by
    refine ⟨c ++ u.tail, v, XWord.append_YWord_tail hc hu, hv, ?_⟩
    have hu_ne := hu.ne_nil
    simp [tail_append_of_ne_nil hu_ne]

lemma length_append_tail {c y : Word} (hy : y ≠ []) :
    (c ++ y.tail).length = c.length + y.length - 1 := by
  have hpos : 1 ≤ y.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil hy)
  simp [length_tail]
  omega

lemma glueIY_of_step {c y0 v : Word} (hy0 : YWord y0) :
    c ++ (y0 ++ r v).tail = (c ++ y0.tail) ++ r v := by
  have : (y0 ++ r v).tail = y0.tail ++ r v :=
    tail_append_of_ne_nil hy0.ne_nil
  rw [this, append_assoc]

lemma isRightParse_glueIY_step {c y0 v : Word} (hc : XWord c)
    (hy0 : YWord y0) (hv : XWord v) :
    IsRightParse (c ++ (y0 ++ r v).tail) (c ++ y0.tail) v :=
  ⟨XWord.append_YWord_tail hc hy0, hv, glueIY_of_step hy0⟩

lemma le_length_of_isRightParse_glueIY_step {c y0 p u v : Word}
    (hc : XWord c) (hy0 : YWord y0) (hp : PWord p)
    (h : IsRightParse (c ++ (y0 ++ r p).tail) u v) :
    p.length ≤ v.length := by
  have h' : IsRightParse ((c ++ y0.tail) ++ r p) u v := by
    simpa [glueIY_of_step hy0] using h
  exact PWord.le_length_of_isRightParse_append_r
    (XWord.append_YWord_tail hc hy0) hp h'

lemma YWord.eq_base_iff_length_one {w : Word} (hw : YWord w) :
    w.length = 1 ↔ w = [0] := by
  constructor
  · exact YWord.eq_base_of_length_one hw
  · intro h
    simp [h]

lemma RIrreducible.not_isRightParse {w u v : Word} (h : RIrreducible w) :
    ¬ IsRightParse w u v :=
  h.2 u v

lemma xword_exists_rIrreducible_yword :
    ∀ n w, w.length = n → XWord w →
      ∃ c y, RIrreducible c ∧ YWord y ∧ w = c ++ y.tail := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen hw
    by_cases hparse : ∃ u v, IsRightParse w u v
    · obtain ⟨u, v, hp, hmin⟩ := exists_shortest_right_parse hparse
      have hvP : PWord v := XWord.of_isRightParse_shortest hp hmin
      have hulen : u.length < n := by
        have := hp.length_add
        have := hp.pos_right
        omega
      obtain ⟨c, y0, hc, hy0, hu⟩ := ih u.length hulen u rfl hp.1
      refine ⟨c, y0 ++ r v, hc, YWord.step hy0 hvP.1, ?_⟩
      rw [glueIY_of_step hy0, ← hu]
      exact hp.2.2
    · refine ⟨w, [0], ⟨hw, fun u v h => hparse ⟨u, v, h⟩⟩, YWord.base, ?_⟩
      simp

lemma eq_of_rIrreducible_yword :
    ∀ n c y c' y', (c ++ y.tail).length = n →
      RIrreducible c → YWord y → RIrreducible c' → YWord y' →
      c ++ y.tail = c' ++ y'.tail → c = c' ∧ y = y' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c y c' y' hlen hc hy hc' hy' heq
    have hyne := hy.ne_nil
    have hy'ne := hy'.ne_nil
    have hy1 : 1 ≤ y.length := hy.xWord.length_ge_one
    have hy1' : 1 ≤ y'.length := hy'.xWord.length_ge_one
    by_cases hy2 : 2 ≤ y.length
    · have hy2' : 2 ≤ y'.length := by
        by_contra hlt
        have hy'len : y'.length = 1 := by omega
        have hy'0 : y' = [0] := YWord.eq_base_of_length_one hy' hy'len
        have hw : c ++ y.tail = c' := by
          simpa [hy'0] using heq
        obtain ⟨u, v, hp⟩ :=
          exists_right_parse_append_YWord_tail hc.xWord hy hy2
        have hp' : IsRightParse c' u v := by
          simpa [hw] using hp
        exact hc'.not_isRightParse hp'
      obtain ⟨y0, p, hpY, hvP, hminY⟩ :=
        YWord.shortest_remainder_is_pword hy hy2
      have hy0Y : YWord y0 := YWord.shortest_left_is_yword hy hpY hminY
      have hyeq : y = y0 ++ r p := hpY.2.2
      have hparse :
          IsRightParse (c ++ y.tail) (c ++ y0.tail) p := by
        rw [hyeq]
        exact isRightParse_glueIY_step hc.xWord hy0Y hvP.1
      have hmin :
          ∀ u2 v2, IsRightParse (c ++ y.tail) u2 v2 →
            p.length ≤ v2.length := by
        intro u2 v2 hp2
        have hp2' : IsRightParse (c ++ (y0 ++ r p).tail) u2 v2 := by
          simpa [hyeq] using hp2
        exact le_length_of_isRightParse_glueIY_step hc.xWord hy0Y hvP hp2'
      obtain ⟨y0', p', hpY', hvP', hminY'⟩ :=
        YWord.shortest_remainder_is_pword hy' hy2'
      have hy0Y' : YWord y0' :=
        YWord.shortest_left_is_yword hy' hpY' hminY'
      have hyeq' : y' = y0' ++ r p' := hpY'.2.2
      have hparse' :
          IsRightParse (c ++ y.tail) (c' ++ y0'.tail) p' := by
        rw [heq, hyeq']
        exact isRightParse_glueIY_step hc'.xWord hy0Y' hvP'.1
      have hmin' :
          ∀ u2 v2, IsRightParse (c ++ y.tail) u2 v2 →
            p'.length ≤ v2.length := by
        intro u2 v2 hp2
        have hp2' : IsRightParse (c' ++ (y0' ++ r p').tail) u2 v2 := by
          rw [← hyeq', ← heq]
          exact hp2
        exact le_length_of_isRightParse_glueIY_step hc'.xWord hy0Y' hvP' hp2'
      obtain ⟨hu, hv⟩ :=
        shortest_right_parse_unique hparse hparse' hmin hmin'
      have hlenu : (c ++ y0.tail).length < n := by
        have hsum := hparse.length_add
        have := hpY.pos_right
        omega
      obtain ⟨hc0, hy00⟩ :=
        ih (c ++ y0.tail).length hlenu c y0 c' y0' rfl hc hy0Y hc' hy0Y' hu
      subst hc0
      subst hy00
      subst hv
      exact ⟨rfl, hyeq.trans hyeq'.symm⟩
    · have hylen : y.length = 1 := by omega
      have hy0 : y = [0] := YWord.eq_base_of_length_one hy hylen
      have hy2' : ¬ 2 ≤ y'.length := by
        intro hy2'
        obtain ⟨u, v, hp⟩ :=
          exists_right_parse_append_YWord_tail hc'.xWord hy' hy2'
        have hp' : IsRightParse c u v := by
          simpa [hy0, heq.symm] using hp
        exact hc.not_isRightParse hp'
      have hy'len : y'.length = 1 := by omega
      have hy'0 : y' = [0] := YWord.eq_base_of_length_one hy' hy'len
      subst hy0
      subst hy'0
      simp at heq
      exact ⟨heq, rfl⟩

def iN (n : ℕ) : Set Word :=
  {w | RIrreducible w ∧ w.length = n}

lemma iN_subset_xN (n : ℕ) : iN n ⊆ xN n :=
  fun _ hw => ⟨hw.1.xWord, hw.2⟩

lemma iN_finite (n : ℕ) : (iN n).Finite :=
  (xN_finite n).subset (iN_subset_xN n)

noncomputable def iNFinset (n : ℕ) : Finset Word :=
  (iN_finite n).toFinset

lemma mem_iNFinset {n : ℕ} {w : Word} :
    w ∈ iNFinset n ↔ w ∈ iN n :=
  Set.Finite.mem_toFinset (iN_finite n)

lemma ncard_iN_eq_card (n : ℕ) :
    (iN n).ncard = (iNFinset n).card :=
  Set.ncard_eq_toFinset_card _ (iN_finite n)

noncomputable def xNFinset (n : ℕ) : Finset Word :=
  (xN_finite n).toFinset

lemma mem_xNFinset {n : ℕ} {w : Word} :
    w ∈ xNFinset n ↔ w ∈ xN n :=
  Set.Finite.mem_toFinset (xN_finite n)

lemma ncard_xN_eq_card (n : ℕ) :
    (xN n).ncard = (xNFinset n).card :=
  Set.ncard_eq_toFinset_card _ (xN_finite n)

lemma disjoint_iNFinset_product {i j k l : ℕ} (hij : i ≠ j) :
    Disjoint (iNFinset i ×ˢ yNFinset k) (iNFinset j ×ˢ yNFinset l) := by
  refine Finset.disjoint_iff_ne.mpr ?_
  intro p hp q hq hpeq
  have hi : p.1.length = i := (mem_iNFinset.mp (Finset.mem_product.mp hp).1).2
  have hj : q.1.length = j := (mem_iNFinset.mp (Finset.mem_product.mp hq).1).2
  have : p.1.length = q.1.length := congrArg List.length (congrArg Prod.fst hpeq)
  omega

noncomputable def iyPairs (n : ℕ) : Finset (Word × Word) :=
  (Finset.Icc 1 n).biUnion fun k =>
    iNFinset k ×ˢ yNFinset (n + 1 - k)

lemma mem_iyPairs {n : ℕ} {p : Word × Word} :
    p ∈ iyPairs n ↔
      ∃ k ∈ Finset.Icc 1 n, p.1 ∈ iN k ∧ p.2 ∈ yN (n + 1 - k) := by
  simp [iyPairs, Finset.mem_biUnion, Finset.mem_product, mem_iNFinset, mem_yNFinset]

lemma card_iyPairs (n : ℕ) :
    (iyPairs n).card =
      ∑ k ∈ Finset.Icc 1 n,
        (iNFinset k).card * (yNFinset (n + 1 - k)).card := by
  have hdisj : (Finset.Icc 1 n : Set ℕ).PairwiseDisjoint
      (fun k => iNFinset k ×ˢ yNFinset (n + 1 - k)) := by
    intro i _ j _ hij
    exact disjoint_iNFinset_product hij
  rw [iyPairs, Finset.card_biUnion hdisj]
  simp [Finset.card_product]

lemma injOn_glueIY_iyPairs (n : ℕ) :
    Set.InjOn (fun p : Word × Word => p.1 ++ p.2.tail) (iyPairs n) := by
  intro p hp q hq heq
  obtain ⟨k, _, hc, hy⟩ := mem_iyPairs.mp hp
  obtain ⟨k', _, hc', hy'⟩ := mem_iyPairs.mp hq
  obtain ⟨h1, h2⟩ :=
    eq_of_rIrreducible_yword (p.1 ++ p.2.tail).length
      p.1 p.2 q.1 q.2 rfl hc.1 hy.1 hc'.1 hy'.1 heq
  exact Prod.ext h1 h2

lemma image_iyPairs (n : ℕ) (hn : 1 ≤ n) :
    (iyPairs n).image (fun p => p.1 ++ p.2.tail) = xNFinset n := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, hk, hc, hy⟩ := mem_iyPairs.mp hp
    have hwX : XWord (p.1 ++ p.2.tail) :=
      XWord.append_YWord_tail hc.1.xWord hy.1
    have hlen : (p.1 ++ p.2.tail).length = n := by
      have hk1 := Finset.mem_Icc.mp hk
      rw [length_append_tail hy.1.ne_nil, hc.2, hy.2]
      omega
    exact mem_xNFinset.mpr ⟨hwX, hlen⟩
  · intro hw
    have hw' := mem_xNFinset.mp hw
    have hlenw : w.length = n := hw'.2
    obtain ⟨c, y, hc, hy, heq⟩ :=
      xword_exists_rIrreducible_yword n w hlenw hw'.1
    have hsum : c.length + y.length - 1 = n := by
      rw [← hlenw, heq, length_append_tail hy.ne_nil]
    have hcpos := hc.xWord.length_pos
    have hypos := hy.xWord.length_pos
    have hk : c.length ∈ Finset.Icc 1 n := by
      simp [Finset.mem_Icc]
      omega
    have huN : c ∈ iN c.length := ⟨hc, rfl⟩
    have hyN : y ∈ yN (n + 1 - c.length) := ⟨hy, by omega⟩
    refine Finset.mem_image.mpr ⟨(c, y), ?_, heq.symm⟩
    exact mem_iyPairs.mpr ⟨c.length, hk, huN, hyN⟩

lemma ncard_xN_eq_sum_iN_yN (n : ℕ) (hn : 1 ≤ n) :
    (xN n).ncard =
      ∑ k ∈ Finset.Icc 1 n, (iN k).ncard * (yN (n + 1 - k)).ncard := by
  have himg := image_iyPairs n hn
  have hinj := injOn_glueIY_iyPairs n
  have hcard : (xNFinset n).card = (iyPairs n).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  rw [ncard_xN_eq_card, hcard, card_iyPairs]
  simp [ncard_iN_eq_card, ncard_yN_eq_card]

lemma ncard_xN_eq_sum_iN_H (n : ℕ) (hn : 1 ≤ n) :
    (xN n).ncard =
      ∑ k ∈ Finset.Icc 1 n, (iN k).ncard * H (n - k) := by
  rw [ncard_xN_eq_sum_iN_yN n hn]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkle : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hy : (yN (n + 1 - k)).ncard = H (n - k) := by
    have hpos : 1 ≤ n + 1 - k := by omega
    have hH := ncard_yN_eq_H_of_pos hpos
    have hidx : n + 1 - k - 1 = n - k := by omega
    simpa [hidx] using hH
  rw [hy]

#print axioms ncard_xN_one
#print axioms ncard_xN_two
#print axioms ncard_xN_three
#print axioms exists_shortest_right_parse
#print axioms PWord.not_isAppend
#print axioms not_xWord_cons_zero_r_of_one_le_head
#print axioms PWord.of_step_right
#print axioms XWord.convex
#print axioms PWord.step_right_factor_nonneg
#print axioms PWord.step_left_factor_nonpos
#print axioms PWord.of_step_left
#print axioms XWord.pword_sign
#print axioms PWord.getElem_neg_of_lt_idxOf
#print axioms PWord.eq_of_isRightParse_cons_zero_r
#print axioms PWord.step_right_of_heads_eq_zero
#print axioms PWord.le_length_of_isRightParse_append_r
#print axioms PWord.getLast_eq_one_of_head_eq_zero
#print axioms PWord.exists_right_parse_of_head_eq_zero
#print axioms XWord.exists_concat_split
#print axioms XWord.of_isRightParse_shortest
#print axioms PWord.of_isRightParse_shortest
#print axioms PWord.shortest_right_parse_factors
#print axioms PWord.remainder_head_eq_zero
#print axioms PWord.eq_of_step_right
#print axioms YWord.shortest_remainder_is_pword
#print axioms ncard_rightN_one
#print axioms ncard_rightN_succ
#print axioms ncard_rightN_succ_eq_catalan
#print axioms ncard_rightN_eq_catalan
#print axioms ncard_pN_eq_catalan
#print axioms YWord.shortest_left_is_yword
#print axioms ncard_yN_one
#print axioms ncard_yN_eq_H
#print axioms sum_H_mul_catalan_succ
#print axioms xword_exists_rIrreducible_yword
#print axioms eq_of_rIrreducible_yword
#print axioms ncard_xN_eq_sum_iN_H
#print axioms PWord.take_idxOf_concat_zero
#print axioms PWord.cons_zero_drop_succ_idxOf
#print axioms PWord.take_idxOf_concat_zero_append_drop
#print axioms PWord.rho
#print axioms PWord.yWord_of_head_eq_zero
#print axioms PWord.append_tail_of_head_eq_zero
#print axioms xN_finite
#print axioms XWord.rho_mem
#print axioms XWord.cons_zero_of_head_eq_neg_one
#print axioms XWord.append_zero_of_getLast_eq_one
#print axioms RIrreducible.getLast_eq_zero
#print axioms XWord.append_YWord_tail
#print axioms exists_right_parse_append_YWord_tail

end OeisA108081
