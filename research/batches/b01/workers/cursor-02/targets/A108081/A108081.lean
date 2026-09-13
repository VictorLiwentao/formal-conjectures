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

#print axioms ncard_xN_one
#print axioms ncard_xN_two
#print axioms xN_finite
#print axioms XWord.rho_mem
#print axioms XWord.cons_zero_of_head_eq_neg_one
#print axioms XWord.append_zero_of_getLast_eq_one
#print axioms RIrreducible.getLast_eq_zero

end OeisA108081
