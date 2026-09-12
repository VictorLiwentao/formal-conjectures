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
AI assistance: Cursor Grok 4.6 Extra High, as a research worker in batch b01.
-/

import FormalConjectures.OEIS.«237271»

/-!
# Proof of `OeisA237271.observation_carmichael`

Frozen source: `FormalConjectures/OEIS/237271.lean` at
`a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
This file restates and proves that declaration from the definitions.
It does not use `OeisA237271.observation_carmichael`, `conjecture_2`, or any
`sorry`-dependent helper.
-/

open Nat Finset List

namespace OeisA237271.Cursor01

/-- Consecutive-divisor jump predicate used by `OeisA237271.a`. -/
def IsJumpPair (pair : ℕ × ℕ) : Prop :=
  Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst

private lemma a_eq (n : ℕ) :
    a n = 1 + ((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).countP
      fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst :=
  rfl

private lemma countP_ge_two_of_getElem {α : Type*} {p : α → Bool} {l : List α}
    (hlen : 2 ≤ l.length)
    (h0 : p (l[0]'(by omega)) = true)
    (h1 : p (l[l.length - 1]'(by omega)) = true) :
    2 ≤ l.countP p := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | x :: y :: rest =>
    have hx : p x = true := by simpa using h0
    rw [countP_cons_of_pos hx]
    have : 0 < (y :: rest).countP p := by
      rw [countP_pos_iff]
      refine ⟨(y :: rest).getLast (by simp), getLast_mem _, ?_⟩
      have hlast :
          (y :: rest).getLast (by simp) =
            (x :: y :: rest)[(x :: y :: rest).length - 1]'(by omega) := by
        simp [getLast_eq_getElem]
      simpa [hlast] using h1
    omega

private lemma fermatPsp_one_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) :
    n.FermatPsp 1 :=
  hn 1 (by omega) (by simp)

private lemma composite_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) :
    n.Composite := by
  obtain ⟨_, hnp, hn1⟩ := fermatPsp_one_of_isCarmichael hn
  exact ⟨hn1, hnp⟩

/-- Carmichael numbers are odd. An even composite would be a Fermat
pseudoprime to the coprime base `n-1 ≡ -1`, forcing `n ∣ 2`. -/
private lemma odd_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) : Odd n := by
  obtain ⟨_, hnp, hn1⟩ := fermatPsp_one_of_isCarmichael hn
  rw [← Nat.not_even_iff_odd]
  intro heven
  have hcop : n.Coprime (n - 1) := by
    rw [coprime_self_sub_right (by omega)]
    simp
  obtain ⟨hpr, _, _⟩ := hn (n - 1) (by omega) hcop
  have hge : 1 ≤ (n - 1) ^ (n - 1) :=
    Nat.one_le_pow (n - 1) (n - 1) (by omega)
  haveI : NeZero n := ⟨by omega⟩
  have hpow :
      ((n - 1 : ZMod n) ^ (n - 1) - 1) = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub hge, ZMod.natCast_eq_zero_iff]
    exact hpr
  have hneg : (n - 1 : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self, zero_sub]
  have hodd : Odd (n - 1) := by
    rw [Nat.odd_iff_not_even, even_sub (by omega : 1 ≤ n)]
    simp [heven]
  have h1 : (-1 : ZMod n) ^ (n - 1) = 1 := by
    rw [← hneg]
    exact eq_of_sub_eq_zero hpow
  have h2 : (-1 : ZMod n) ^ (n - 1) = -1 := hodd.neg_one_pow
  have : (2 : ZMod n) = 0 := by
    have hneg1 : (-1 : ZMod n) = 1 := by
      rw [← h2, h1]
    have := congrArg (fun x : ZMod n => x + 1) hneg1
    simpa using this
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).1 this
  rcases (dvd_prime prime_two).1 hdvd with h | h
  · exact absurd h (by omega)
  · exact hnp (h ▸ prime_two)

private lemma three_le_card_divisors_of_composite {n : ℕ} (h : n.Composite) :
    3 ≤ n.divisors.card := by
  obtain ⟨hn1, hnp⟩ := h
  have hn2 : 2 ≤ n := Nat.succ_le_of_lt hn1
  obtain ⟨m, hmd, hm2, hmlt⟩ := exists_dvd_of_not_prime2 hn2 hnp
  have hn0 : n ≠ 0 := by omega
  have h1mem : 1 ∈ n.divisors := one_mem_divisors.mpr hn0
  have hmmem : m ∈ n.divisors := mem_divisors.mpr ⟨hmd, hn0⟩
  have hnmem : n ∈ n.divisors := mem_divisors_self n hn0
  have hne1 : (1 : ℕ) ≠ m := ne_of_lt hm2
  have h1n : (1 : ℕ) ≠ n := ne_of_gt hn1
  have hmn : m ≠ n := ne_of_lt hmlt
  have hsubset : ({1, m, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1mem
    · exact hmmem
    · exact hnmem
  have hcard : #({1, m, n} : Finset ℕ) = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simp [hmn]
    · simp [h1n, hne1]
  exact hcard ▸ card_le_card hsubset

private lemma sorted_divisors_zero {n : ℕ} (hn0 : n ≠ 0)
    (hpos : 0 < (n.divisors.sort (· ≤ ·)).length) :
    (n.divisors.sort (· ≤ ·))[0] = 1 := by
  have hne : n.divisors.Nonempty := ⟨1, one_mem_divisors.mpr hn0⟩
  rw [sorted_zero_eq_min']
  apply le_antisymm
  · exact min'_le _ 1 (one_mem_divisors.mpr hn0)
  · have : 0 < n.divisors.min' hne := pos_of_mem_divisors (min'_mem _ _)
    omega

private lemma sorted_divisors_last {n : ℕ} (hn0 : n ≠ 0)
    (hlast : (n.divisors.sort (· ≤ ·)).length - 1 < (n.divisors.sort (· ≤ ·)).length) :
    (n.divisors.sort (· ≤ ·))[(n.divisors.sort (· ≤ ·)).length - 1] = n := by
  have hne : n.divisors.Nonempty := ⟨1, one_mem_divisors.mpr hn0⟩
  rw [sorted_last_eq_max']
  apply le_antisymm
  · exact divisor_le (max'_mem _ _)
  · exact le_max' _ n (mem_divisors_self n hn0)

private lemma two_mul_le_of_proper_dvd {d n : ℕ} (hdvd : d ∣ n) (hlt : d < n) :
    2 * d ≤ n := by
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    have : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le d) hlt
    exact Nat.pos_of_mul_pos_left (hk ▸ this)
  have hk1 : 1 < k := by
    rw [← not_le]
    intro hk1
    have : k = 1 := by omega
    exact (ne_of_lt hlt) (by simp [hk, this])
  calc
    2 * d ≤ k * d := Nat.mul_le_mul_right d hk1
    _ = n := by rw [hk, mul_comm]

/-- Ordered-divisor structural lemma: every odd composite has at least two
consecutive divisor pairs counted by `a`. -/
theorem a_ge_three_of_odd_composite {n : ℕ} (hcomp : n.Composite) (hodd : Odd n) :
    3 ≤ a n := by
  set d := n.divisors.sort (· ≤ ·) with hd
  set pairs := d.zip d.tail with hpairs
  have hn0 : n ≠ 0 := by
    obtain ⟨hn1, _⟩ := hcomp
    omega
  have hcard : 3 ≤ n.divisors.card := three_le_card_divisors_of_composite hcomp
  have hlen : 3 ≤ d.length := by
    simpa [hd, length_sort] using hcard
  have hplen : 2 ≤ pairs.length := by
    have : pairs.length = d.length - 1 := by
      simp [hpairs, length_zip, length_tail]
      omega
    omega
  have hjump0 : Odd (pairs[0]'(by omega)).snd ∧
      (pairs[0]'(by omega)).snd ≥ 2 * (pairs[0]'(by omega)).fst := by
    have h0 : 0 < d.length := by omega
    have h1 : 1 < d.length := by omega
    have hzi : 0 < pairs.length := by omega
    have hz : pairs[0] = (d[0], d.tail[0]'(by simp [length_tail]; omega)) := by
      simp [hpairs, getElem_zip]
    have hd0 : d[0] = 1 := sorted_divisors_zero hn0 (by omega)
    have hd1 : d.tail[0]'(by simp [length_tail]; omega) = d[1] := by
      simp [getElem_tail]
    have hmem1 : d[1] ∈ n.divisors := (mem_sort (· ≤ ·)).1 (getElem_mem _)
    have hlt01 : d[0] < d[1] := by
      have hpw := sortedLT_sort n.divisors
      have := hpw.rel_get_of_lt (a := ⟨0, by simpa [hd] using h0⟩)
          (b := ⟨1, by simpa [hd] using h1⟩) (by omega)
      simpa [hd, List.get_eq_getElem] using this
    have hodd1 : Odd d[1] := Odd.of_dvd_nat hodd (dvd_of_mem_divisors hmem1)
    have hge : d[1] ≥ 2 * d[0] := by
      have : 2 ≤ d[1] := by
        have : 1 < d[1] := by simpa [hd0] using hlt01
        omega
      simpa [hd0, two_mul] using this
    simpa [hz, hd1] using And.intro hodd1 hge
  have hjumplast : Odd (pairs[pairs.length - 1]'(by omega)).snd ∧
      (pairs[pairs.length - 1]'(by omega)).snd ≥
        2 * (pairs[pairs.length - 1]'(by omega)).fst := by
    have hi : pairs.length - 1 < pairs.length := by omega
    have hdi : d.length - 1 < d.length := by omega
    have hdt : pairs.length - 1 < d.tail.length := by
      have : pairs.length = min d.length d.tail.length := by simp [hpairs, length_zip]
      have : d.tail.length = d.length - 1 := length_tail
      omega
    have hz : pairs[pairs.length - 1] =
        (d[pairs.length - 1]'(by
            have : pairs.length = min d.length d.tail.length := by simp [hpairs, length_zip]
            omega),
          d.tail[pairs.length - 1]'(hdt)) := by
      simp [hpairs, getElem_zip]
    have hlenp : pairs.length = d.length - 1 := by
      simp [hpairs, length_zip, length_tail]
      omega
    have hfst : d[pairs.length - 1]'(by
        have : pairs.length = min d.length d.tail.length := by simp [hpairs, length_zip]
        omega) = d[d.length - 2]'(by omega) := by
      simp [hlenp]
    have hsnd : d.tail[pairs.length - 1]'(hdt) = d[d.length - 1]'(hdi) := by
      simp [getElem_tail, hlenp]
    have hmax : d[d.length - 1]'(hdi) = n := sorted_divisors_last hn0 hdi
    have hmem : d[d.length - 2]'(by omega) ∈ n.divisors :=
      (mem_sort (· ≤ ·)).1 (getElem_mem _)
    have hlt : d[d.length - 2]'(by omega) < n := by
      have hpw := sortedLT_sort n.divisors
      have := hpw.rel_get_of_lt
          (a := ⟨d.length - 2, by simpa [hd] using (by omega : d.length - 2 < d.length)⟩)
          (b := ⟨d.length - 1, by simpa [hd] using hdi⟩) (by omega)
      have hmax' : d.get ⟨d.length - 1, by simpa [hd] using hdi⟩ = n := by
        simpa [hd, List.get_eq_getElem] using hmax
      simpa [hd, List.get_eq_getElem, hmax'] using this
    have hoddn : Odd n := hodd
    have hge : n ≥ 2 * d[d.length - 2]'(by omega) :=
      two_mul_le_of_proper_dvd (dvd_of_mem_divisors hmem) hlt
    refine And.intro ?_ ?_
    · simpa [hz, hsnd, hmax] using hoddn
    · simpa [hz, hsnd, hmax, hfst] using hge
  have hcount : 2 ≤ pairs.countP fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst := by
    refine countP_ge_two_of_getElem hplen ?_ ?_
    · exact decide_eq_true hjump0
    · exact decide_eq_true hjumplast
  have : 3 ≤ 1 + pairs.countP fun pair => Odd pair.snd ∧ pair.snd ≥ 2 * pair.fst := by
    omega
  simpa [a_eq, hd, hpairs] using this

/-- Exact frozen type of `OeisA237271.observation_carmichael`. -/
theorem observation_carmichael (k : ℕ) (hk : IsCarmichael k) : 3 ≤ a k :=
  a_ge_three_of_odd_composite (composite_of_isCarmichael hk) (odd_of_isCarmichael hk)

#print axioms observation_carmichael
#print axioms a_ge_three_of_odd_composite

end OeisA237271.Cursor01
