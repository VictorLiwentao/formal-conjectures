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

lemma XWord.append_zero_of_getLast_eq_one {w : Word} (hw : XWord w)
    (h : w.getLast hw.ne_nil = 1) : XWord (w ++ [0]) := by
  obtain ⟨u, v, hu, hv, hw'⟩ := exists_right_parse_of_getLast_eq_one hw h
  have : w ++ [0] = u ++ r ([-1] ++ v) := by
    rw [hw', r_concat_neg_one, append_assoc]
  rw [this]
  exact XWord.step_right hu (XWord.concat_neg_one hv)

-- Small lengths

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

lemma YWord.exists_right_parse_of_length_ge_two {w : Word} (hw : YWord w)
    (hlen : 2 ≤ w.length) : ∃ u v, IsRightParse w u v :=
  match w, hw with
  | _, .base => by
    simp at hlen
  | _, @YWord.step u v hu hv =>
    ⟨u, v, hu.xWord, hv, rfl⟩

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
