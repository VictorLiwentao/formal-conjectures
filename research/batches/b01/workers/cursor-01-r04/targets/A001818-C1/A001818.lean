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
New Lean proof development and write-up: Wentao Li.
Mathematics: Yue-Feng She, Zhi-Wei Sun and Wei Xia,
A novel permanent identity with applications, arXiv:2208.12167v2,
Theorem 1.3(ii) (even-size case). Dependency: Guo–Li–Tao–Wei,
arXiv:2206.02592; Calogero–Perelomov, Linear Algebra Appl. 25 (1979).
This file treats only OeisA1818.conjecture1. It does not treat conjecture2,
A002454, or A356041 as assigned targets. It does not claim new informal
mathematics or first-formalization priority.
AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.
-/

import FormalConjectures.OEIS.«1818»

/-!
Exact target: `OeisA1818.conjecture1` from frozen
`FormalConjectures/OEIS/1818.lean`.
-/

open Complex Equiv Finset Matrix

namespace A001818C1

open OeisA1818

/-- The source matrix. The wrapper never uses the admitted source theorem. -/
noncomputable def sunMatrix (n : ℕ) (ζ : ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j =>
    if i = j then
      (1 : ℂ)
    else
      (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))

/-- Integer ascription on `i.val - j.val` is `ℤ` subtraction, not truncated `ℕ`. -/
theorem int_sub_val {n : ℕ} (i j : Fin n) :
    (i.val - j.val : ℤ) = (i.val : ℤ) - (j.val : ℤ) := rfl

theorem sunMatrix_eq_frozen (n : ℕ) (ζ : ℂ) :
    sunMatrix n ζ = fun (i j : Fin (2 * n)) =>
      if i = j then
        (1 : ℂ)
      else
        (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ)) :=
  rfl

lemma zeta_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) : ζ ≠ 0 := by
  intro h
  have := hζ.pow_eq_one
  rw [h, zero_pow (NeZero.ne N)] at this
  exact zero_ne_one this

lemma zpow_int_val_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) : ζ ^ (i.val - j.val : ℤ) = ζ ^ (i - j).val := by
  have hz := zeta_ne_zero hζ
  have hN : ζ ^ (N : ℤ) = 1 := by rw [zpow_natCast, hζ.pow_eq_one]
  have hite := Fin.intCast_val_sub_eq_sub_add_ite (n := N) i j
  rw [← zpow_natCast, hite, zpow_add₀ hz]
  split_ifs with hle
  · simp
  · rw [hN, mul_one]

lemma abs_val_sub_lt {N : ℕ} (i j : Fin N) : |(i.val : ℤ) - j.val| < N := by
  have hi := i.isLt
  have hj := j.isLt
  rw [abs_sub_lt_iff]
  constructor <;> omega

lemma zpow_sub_ne_one {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) : ζ ^ (i.val - j.val : ℤ) ≠ 1 := by
  intro h
  have hdvd : (N : ℤ) ∣ (i.val - j.val : ℤ) := (hζ.zpow_eq_one_iff_dvd _).1 h
  have hne : (i.val : ℤ) - j.val ≠ 0 := by
    intro h0
    exact hij (Fin.ext (Int.natCast_inj.mp (sub_eq_zero.mp h0)))
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k = 0 := by
    have hNpos : (0 : ℤ) < N := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
    by_contra hkne
    have hmul : |k| * (N : ℤ) < N := by
      have h' : |(N : ℤ) * k| < N := by
        simpa [hk] using abs_val_sub_lt i j
      simpa [abs_mul, Nat.abs_cast, mul_comm] using h'
    have hge : (N : ℤ) ≤ |k| * N :=
      le_mul_of_one_le_left (le_of_lt hNpos) (Int.one_le_abs hkne)
    exact (not_le.mpr hmul) hge
  exact hne (by simp [hk, hk0])

lemma denom_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) : 1 - ζ ^ (i.val - j.val : ℤ) ≠ 0 := by
  exact sub_ne_zero.2 (zpow_sub_ne_one hζ hij).symm

lemma sunMatrix_apply_ne {n : ℕ} [NeZero n] {ζ : ℂ} (_hζ : IsPrimitiveRoot ζ (2 * n))
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    sunMatrix n ζ i j =
      (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  simp [sunMatrix, hij]

lemma sunMatrix_apply_eq {n : ℕ} (ζ : ℂ) (i : Fin (2 * n)) :
    sunMatrix n ζ i i = 1 := by
  simp [sunMatrix]

/- Permanent of size 2, and the `n = 1` case. -/

lemma univ_perm_fin_two :
    (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap (0 : Fin 2) 1} := by
  ext σ
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have fin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by
    fin_cases x <;> simp
  rcases fin2 (σ 0) with h0 | h0 <;> rcases fin2 (σ 1) with h1 | h1
  · have := σ.injective (h0.trans h1.symm)
    exact absurd this (by decide : (0 : Fin 2) ≠ 1)
  · left
    ext x
    fin_cases x <;> simp [h0, h1]
  · right
    ext x
    fin_cases x <;> simp [h0, h1]
  · have := σ.injective (h0.trans h1.symm)
    exact absurd this (by decide : (0 : Fin 2) ≠ 1)

lemma permanent_fin_two {R : Type*} [CommSemiring R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  have hne : (1 : Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have := congr_fun (congr_arg (fun f : Perm (Fin 2) => (f : Fin 2 → Fin 2)) h) 0
    simp at this
  simp [permanent, univ_perm_fin_two, Fin.prod_univ_two, hne]

lemma a_one : a 1 = 1 := by
  simp [a]

/-- Direct evaluation of C1 at `n = 1`. Primitive 2nd roots are `-1`. -/
theorem conjecture1_of_one {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 2) :
    (sunMatrix 1 ζ).permanent = (a 1 : ℂ) := by
  have hζ' : ζ = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right hζ
  rw [hζ', a_one]
  have hM : sunMatrix 1 (-1) = (1 : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℂ) := by
    ext i j
    by_cases hij : i = j
    · simp [sunMatrix, hij, Matrix.one_apply]
    · have hpow' : (-1 : ℂ) ^ (i.val - j.val : ℤ) = -1 := by
        have : (i.val - j.val : ℤ) = 1 ∨ (i.val - j.val : ℤ) = -1 := by
          fin_cases i <;> fin_cases j <;> simp_all
        rcases this with h | h <;> simp [h]
      simp [sunMatrix, hij, hpow', Matrix.one_apply_ne hij]
  rw [hM, permanent_one, Nat.cast_one]

/- Arithmetic-geometric sums for roots of unity. -/

lemma geom_sum_eq_zero_of_pow_eq_one {x : ℂ} {m : ℕ} (_hm : 1 < m) (hx1 : x ≠ 1)
    (hxm : x ^ m = 1) : ∑ k ∈ range m, x ^ k = 0 := by
  rw [geom_sum_eq hx1, hxm, sub_self, zero_div]

lemma sum_nat_mul_geom {x : ℂ} {m : ℕ} (hm : 1 < m) (hx1 : x ≠ 1) (hxm : x ^ m = 1) :
    ∑ k ∈ range m, (k : ℂ) * x ^ k = m / (x - 1) := by
  have S := geom_sum_eq_zero_of_pow_eq_one hm hx1 hxm
  set T := ∑ k ∈ range m, (k : ℂ) * x ^ k
  have hxT : x * T = ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) := by
    simp only [T, mul_sum, pow_succ]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hshift :
      ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) =
        ∑ j ∈ Icc 1 m, ((j : ℂ) - 1) * x ^ j := by
    refine sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_range, mem_Icc] at hk ⊢
      omega
    · intro a _ha b _hb h
      exact Nat.succ_injective h
    · intro j hj
      simp only [mem_Icc] at hj
      exact ⟨j - 1, by
        simp only [mem_range]
        omega, by omega⟩
    · intro k _hk
      simp
  have hsplit :
      ∑ j ∈ Icc 1 m, ((j : ℂ) - 1) * x ^ j =
        ∑ j ∈ Icc 1 (m - 1), ((j : ℂ) - 1) * x ^ j + ((m : ℂ) - 1) * x ^ m := by
    have hdis : m ∉ Icc 1 (m - 1) := by
      simp only [mem_Icc, not_and, not_le]
      omega
    have hunion : Icc 1 m = insert m (Icc 1 (m - 1)) := by
      ext t
      simp only [mem_insert, mem_Icc]
      omega
    rw [hunion, sum_insert hdis, add_comm]
  have hmid :
      ∑ j ∈ Icc 1 (m - 1), ((j : ℂ) - 1) * x ^ j =
        ∑ j ∈ range m, ((j : ℂ) - 1) * x ^ j + 1 := by
    have h0 : (0 : ℕ) ∉ Icc 1 (m - 1) := by simp
    have : range m = insert 0 (Icc 1 (m - 1)) := by
      ext t
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [this, sum_insert h0]
    simp [sub_mul]
  have hdiff : T - ∑ k ∈ range m, (k : ℂ) * x ^ (k + 1) = -m := by
    rw [hshift, hsplit, hxm, mul_one, hmid]
    have : ∑ j ∈ range m, ((j : ℂ) - 1) * x ^ j =
        T - ∑ j ∈ range m, x ^ j := by
      simp [T, sub_mul, sum_sub_distrib]
    rw [this, S]
    ring
  have hfac : T * (1 - x) = -m := by
    convert hdiff using 1
    rw [← hxT]
    ring
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hmul : T * (x - 1) = m := by
    have hx : x - 1 = -(1 - x) := by ring
    rw [hx, mul_neg, hfac, neg_neg]
  exact eq_div_of_mul_eq hxsub hmul

lemma inv_one_sub_eq_sum {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) :
    (1 - ζ ^ k)⁻¹ = -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
  have hN : 1 < N := by
    have : 0 < N := Nat.pos_of_neZero N
    omega
  have hx1 : ζ ^ k ≠ 1 := by
    intro h
    have := (hζ.pow_eq_one_iff_dvd k).1 h
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk this
  have hpow : (ζ ^ k) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum := sum_nat_mul_geom (x := ζ ^ k) hN hx1 hpow
  have heq : (range N).erase 0 = Icc 1 (N - 1) := by
    ext t
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  have hr : ∑ j ∈ range N, (j : ℂ) * (ζ ^ k) ^ j =
      ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
    have h0 : (0 : ℕ) ∈ range N := mem_range.2 (Nat.pos_of_neZero N)
    let f : ℕ → ℂ := fun j => (j : ℂ) * (ζ ^ k) ^ j
    have hsplit := sum_erase_add (s := range N) (f := f) h0
    have hf0 : f 0 = 0 := by simp [f]
    have : ∑ j ∈ (range N).erase 0, f j = ∑ j ∈ range N, f j := by
      rw [← hsplit, hf0, add_zero]
    rw [heq] at this
    exact this.symm
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hxsub : ζ ^ k - 1 ≠ 0 := sub_ne_zero.2 hx1
  have hsum' : ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j =
      (N : ℂ) / (ζ ^ k - 1) := by
    rw [← hr, hsum]
  have hneg : (1 - ζ ^ k)⁻¹ = - (ζ ^ k - 1)⁻¹ := by
    have : 1 - ζ ^ k = - (ζ ^ k - 1) := by ring
    rw [this, inv_neg]
  have hinv : (ζ ^ k - 1)⁻¹ =
      (N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
    rw [hsum']
    field_simp [hN0, hxsub]
  rw [hneg, hinv]
  ring

/- Type of the frozen source theorem, with `sunMatrix` in place of the inline matrix. -/
#check (OeisA1818.conjecture1 :
    ∀ (n : ℕ), 1 ≤ n → ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      (sunMatrix n ζ).permanent = (a n : ℂ))

#print axioms conjecture1_of_one
#print axioms zpow_sub_ne_one
#print axioms inv_one_sub_eq_sum
#print axioms denom_ne_zero

end A001818C1

