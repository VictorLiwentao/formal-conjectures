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

lemma zeta_pow_ne_one_of_lt {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) : ζ ^ k ≠ 1 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk ((hζ.pow_eq_one_iff_dvd k).1 h)

lemma inv_one_sub_add_inv_one_sub_inv {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < N) :
    (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹ = 1 := by
  have h1 := zeta_pow_ne_one_of_lt hζ hk0 hk
  have hz : ζ ≠ 0 := by
    intro h
    have := hζ.pow_eq_one
    have hN : N ≠ 0 := ne_of_gt (lt_of_le_of_lt (Nat.zero_le k) hk)
    rw [h, zero_pow hN] at this
    exact zero_ne_one this
  have hsum : ζ ^ k * ζ ^ (N - k) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le (le_of_lt hk), hζ.pow_eq_one]
  have hNk : (ζ ^ k)⁻¹ = ζ ^ (N - k) := inv_eq_of_mul_eq_one_right hsum
  have hz0 : ζ ^ k ≠ 0 := pow_ne_zero k hz
  have hz1 : 1 - ζ ^ k ≠ 0 := sub_ne_zero.2 h1.symm
  have hform : 1 - (ζ ^ k)⁻¹ = (ζ ^ k - 1) / ζ ^ k := by
    field_simp [hz0]
  calc
    (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹
        = (1 - ζ ^ k)⁻¹ + (1 - (ζ ^ k)⁻¹)⁻¹ := by rw [hNk]
    _ = (1 - ζ ^ k)⁻¹ + ((ζ ^ k - 1) / ζ ^ k)⁻¹ := by rw [hform]
    _ = (1 - ζ ^ k)⁻¹ + ζ ^ k / (ζ ^ k - 1) := by rw [inv_div]
    _ = (1 - ζ ^ k)⁻¹ + ζ ^ k / -(1 - ζ ^ k) := by ring
    _ = (1 - ζ ^ k)⁻¹ - ζ ^ k / (1 - ζ ^ k) := by
          rw [div_neg]
          ring
    _ = 1 := by field_simp [hz1]

lemma mem_Icc_one_pred_sub {N k : ℕ} (hk : k ∈ Icc 1 (N - 1)) :
    N - k ∈ Icc 1 (N - 1) := by
  simp only [mem_Icc] at hk ⊢
  have hkN : k ≤ N := le_trans hk.2 (Nat.sub_le N 1)
  constructor
  · exact (Nat.le_sub_iff_add_le hkN).mpr (by omega)
  · exact tsub_le_tsub_left hk.1 N

lemma card_Icc_one_pred {N : ℕ} (hN : 1 < N) :
    ((Icc 1 (N - 1)).card : ℂ) = (N - 1 : ℂ) := by
  rw [Nat.card_Icc]
  have : N - 1 + 1 - 1 = N - 1 := by omega
  rw [this, Nat.cast_sub (le_of_lt hN), Nat.cast_one]

lemma sum_inv_one_sub_eq_half {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) :
    ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ = (N - 1 : ℂ) / 2 := by
  have hconst : ∀ k ∈ Icc 1 (N - 1),
      (1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹ = 1 := by
    intro k hk
    simp only [mem_Icc] at hk
    exact inv_one_sub_add_inv_one_sub_inv hζ (by omega) (by omega)
  have hpair : ∑ k ∈ Icc 1 (N - 1),
      ((1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹) = (N - 1 : ℂ) := by
    rw [sum_congr rfl hconst, sum_const, nsmul_one, card_Icc_one_pred hN]
  have hreindex : ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ (N - k))⁻¹ =
      ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ := by
    refine sum_bij (fun k _ => N - k) (fun k hk => mem_Icc_one_pred_sub hk) ?_ ?_ ?_
    · intro a ha b hb h
      simp only [mem_Icc] at ha hb
      have haN : a ≤ N := le_trans ha.2 (Nat.sub_le N 1)
      have hbN : b ≤ N := le_trans hb.2 (Nat.sub_le N 1)
      exact (tsub_right_inj haN hbN).1 h
    · intro k hk
      refine ⟨N - k, mem_Icc_one_pred_sub hk, ?_⟩
      simp only [mem_Icc] at hk
      exact Nat.sub_sub_self (le_trans hk.2 (Nat.sub_le N 1))
    · intro _ _
      rfl
  have htwo : 2 * ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ = (N - 1 : ℂ) := by
    calc
      2 * ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹
          = ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ +
              ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ := by rw [two_mul]
      _ = ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ k)⁻¹ +
              ∑ k ∈ Icc 1 (N - 1), (1 - ζ ^ (N - k))⁻¹ := by rw [hreindex]
      _ = ∑ k ∈ Icc 1 (N - 1),
            ((1 - ζ ^ k)⁻¹ + (1 - ζ ^ (N - k))⁻¹) := sum_add_distrib.symm
      _ = (N - 1 : ℂ) := hpair
  exact eq_div_of_mul_eq two_ne_zero (by rw [mul_comm]; exact htwo)

lemma range_eq_insert_zero_Icc {N : ℕ} (hN : 1 < N) :
    range N = insert 0 (Icc 1 (N - 1)) := by
  ext t
  simp only [mem_range, mem_insert, mem_Icc]
  omega

lemma sum_Icc_pow {x : ℂ} {N : ℕ} (hN : 1 < N) (hxN : x ^ N = 1) :
    ∑ k ∈ Icc 1 (N - 1), x ^ k = if x = 1 then (N - 1 : ℂ) else -1 := by
  have h0 : (0 : ℕ) ∉ Icc 1 (N - 1) := by simp
  have hsum : ∑ k ∈ range N, x ^ k = 1 + ∑ k ∈ Icc 1 (N - 1), x ^ k := by
    rw [range_eq_insert_zero_Icc hN, sum_insert h0, pow_zero]
  split_ifs with hx
  · subst hx
    simp [sum_const]
    rw [Nat.cast_sub (le_of_lt hN), Nat.cast_one]
  · have h0sum : ∑ k ∈ range N, x ^ k = 0 :=
      geom_sum_eq_zero_of_pow_eq_one hN hx hxN
    have hadd : 1 + ∑ k ∈ Icc 1 (N - 1), x ^ k = 0 := by rw [← hsum, h0sum]
    rw [add_comm] at hadd
    exact eq_neg_of_add_eq_zero_left hadd

lemma sum_Icc_zeta_pow {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (m : ℕ) :
    ∑ t ∈ Icc 1 (N - 1), (ζ ^ m) ^ t = if N ∣ m then (N - 1 : ℂ) else -1 := by
  have hxN : (ζ ^ m) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [sum_Icc_pow hN hxN]
  simp [hζ.pow_eq_one_iff_dvd]

lemma sum_Icc_cast {N : ℕ} (hN : 1 < N) :
    ∑ k ∈ Icc 1 (N - 1), (k : ℂ) = (N : ℂ) * (N - 1) / 2 := by
  have h0 : (0 : ℕ) ∉ Icc 1 (N - 1) := by simp
  have hsum : ∑ k ∈ range N, (k : ℂ) = ∑ k ∈ Icc 1 (N - 1), (k : ℂ) := by
    rw [range_eq_insert_zero_Icc hN, sum_insert h0]
    simp
  have hnat := congrArg (fun n : ℕ => (n : ℂ)) (sum_range_id_mul_two N)
  simp only [Nat.cast_mul, Nat.cast_two, Nat.cast_sub (le_of_lt hN)] at hnat
  rw [Nat.cast_sum, Nat.cast_one] at hnat
  exact eq_div_of_mul_eq two_ne_zero (by rw [← hsum]; convert hnat using 1)

lemma zpow_neg_mul_eq_pow_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (r : Fin N) (k : ℕ) :
    ζ ^ ((-(r.val : ℤ)) * k) = (ζ ^ (N - r.val)) ^ k := by
  have hz := zeta_ne_zero hζ
  have hr : r.val ≤ N := le_of_lt r.isLt
  have hexp : ((-(r.val : ℤ)) * k) = (N - (r.val : ℤ)) * k - (N : ℤ) * k := by ring
  have hcast : (N : ℤ) - r.val = ((N - r.val : ℕ) : ℤ) := (Nat.cast_sub hr).symm
  have hNk : ζ ^ (N * k) = 1 := by
    rw [pow_mul, hζ.pow_eq_one, one_pow]
  have hL : ζ ^ (((N - r.val : ℕ) : ℤ) * k) = (ζ ^ (N - r.val)) ^ k := by
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
  have hR : ζ ^ ((N : ℤ) * k) = ζ ^ (N * k) := by
    rw [← Nat.cast_mul, zpow_natCast]
  calc
    ζ ^ ((-(r.val : ℤ)) * k)
        = ζ ^ ((N - (r.val : ℤ)) * k - (N : ℤ) * k) := by rw [hexp]
    _ = ζ ^ (((N - r.val : ℕ) : ℤ) * k - (N : ℤ) * k) := by rw [hcast]
    _ = ζ ^ (((N - r.val : ℕ) : ℤ) * k) / ζ ^ ((N : ℤ) * k) := zpow_sub₀ hz _ _
    _ = (ζ ^ (N - r.val)) ^ k / ζ ^ (N * k) := by rw [hL, hR]
    _ = (ζ ^ (N - r.val)) ^ k := by rw [hNk, div_one]

/-- Zero-diagonal Calogero circulant: off-diagonal `2 / (1 - ζ^{i-j})`. -/
noncomputable def calogero (N : ℕ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then 0 else 2 / (1 - ζ ^ (i.val - j.val : ℤ))

lemma calogero_apply_eq {N : ℕ} (ζ : ℂ) (i : Fin N) : calogero N ζ i i = 0 := by
  simp [calogero]

lemma calogero_apply_ne {N : ℕ} {ζ : ℂ} {i j : Fin N} (hij : i ≠ j) :
    calogero N ζ i j = 2 / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  simp [calogero, hij]

lemma eq_of_dvd_of_bounds {N m : ℕ} (hN : 1 < N) (h2 : 2 ≤ m) (hmax : m ≤ 2 * N - 2)
    (hdvd : N ∣ m) : m = N := by
  obtain ⟨t, rfl⟩ := hdvd
  have : t = 1 := by
    have hpos : t ≠ 0 := by
      rintro rfl
      simp at h2
    have hle1 : t ≤ 1 := by
      by_contra ht
      have : 2 ≤ t := by omega
      have hmul : N * 2 ≤ N * t := Nat.mul_le_mul_left N this
      have : 2 * N ≤ 2 * N - 2 := by
        rw [mul_comm N 2] at hmul
        exact le_trans hmul hmax
      omega
    omega
  simp [this]

lemma dvd_add_sub_iff {N j r : ℕ} (hN : 1 < N) (hj1 : 1 ≤ j) (hj : j < N)
    (hr0 : 0 < r) (hr : r < N) :
    N ∣ j + (N - r) ↔ j = r := by
  have hle : r ≤ N := le_of_lt hr
  constructor
  · intro h
    have h2 : 2 ≤ j + (N - r) := by omega
    have hmax : j + (N - r) ≤ 2 * N - 2 := by omega
    have hm : j + (N - r) = N := eq_of_dvd_of_bounds hN h2 hmax h
    omega
  · intro h
    subst h
    simp [Nat.add_sub_of_le hle]

lemma sum_cast_mul_ite {N r : ℕ} (hr : r ∈ Icc 1 (N - 1)) :
    ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) =
      -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r : ℂ) * N := by
  have hsplit :=
    (sum_erase_add (s := Icc 1 (N - 1))
      (f := fun j => (j : ℂ) * (if j = r then (N - 1 : ℂ) else (-1 : ℂ))) hr).symm
  have herase :
      ∑ j ∈ (Icc 1 (N - 1)).erase r,
          (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) =
        ∑ j ∈ (Icc 1 (N - 1)).erase r, -(j : ℂ) := by
    refine sum_congr rfl fun j hj => ?_
    have : j ≠ r := (mem_erase.mp hj).1
    simp [this]
  have hsum :
      ∑ j ∈ Icc 1 (N - 1), (j : ℂ) =
        ∑ j ∈ (Icc 1 (N - 1)).erase r, (j : ℂ) + r := by
    simpa using
      (sum_erase_add (s := Icc 1 (N - 1)) (f := fun j => (j : ℂ)) hr).symm
  calc
    ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1)
        = ∑ j ∈ (Icc 1 (N - 1)).erase r,
              (j : ℂ) * (if j = r then (N - 1 : ℂ) else -1) +
            (r : ℂ) * (if r = r then (N - 1 : ℂ) else -1) := hsplit
    _ = ∑ j ∈ (Icc 1 (N - 1)).erase r, -(j : ℂ) + (r : ℂ) * (N - 1) := by
          rw [herase, if_pos rfl]
    _ = -∑ j ∈ (Icc 1 (N - 1)).erase r, (j : ℂ) + (r : ℂ) * (N - 1) := by
          rw [sum_neg_distrib]
    _ = -(∑ j ∈ Icc 1 (N - 1), (j : ℂ) - r) + (r : ℂ) * (N - 1) := by
          rw [hsum]; ring
    _ = -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r : ℂ) * N := by ring

/-- Eigenvalue `N - 1 - 2 r` of the Calogero circulant, as a kernel sum. -/
lemma calogero_kernel_sum {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (r : Fin N) :
    ∑ k ∈ Icc 1 (N - 1), 2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
      (N : ℂ) - 1 - 2 * r.val := by
  by_cases hr : r = 0
  · subst hr
    simp [neg_zero, zero_mul, ← mul_sum]
    rw [sum_inv_one_sub_eq_half hζ hN]
    ring
  · have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
    have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr0
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hterm :
        ∑ k ∈ Icc 1 (N - 1), 2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
          2 * ∑ k ∈ Icc 1 (N - 1),
            (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ := by
      have hpt : ∀ k ∈ Icc 1 (N - 1),
          2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹ =
            2 * ((ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹) := by
        intro k _
        rw [zpow_neg_mul_eq_pow_sub hζ r k]
        ring
      rw [sum_congr rfl hpt, mul_sum]
    rw [hterm]
    have hinv : ∀ k ∈ Icc 1 (N - 1),
        (1 - ζ ^ k)⁻¹ =
          -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j := by
      intro k hk
      simp only [mem_Icc] at hk
      exact inv_one_sub_eq_sum hζ (by omega) (by omega)
    have hswap :
        ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ =
          -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) *
            ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t := by
      have h1 :
          ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k * (1 - ζ ^ k)⁻¹ =
            ∑ k ∈ Icc 1 (N - 1), (ζ ^ (N - r.val)) ^ k *
              (-(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j) :=
        sum_congr rfl fun k hk => by rw [hinv k hk]
      rw [h1]
      have hpt : ∀ k ∈ Icc 1 (N - 1),
          (ζ ^ (N - r.val)) ^ k *
              (-(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1), (j : ℂ) * (ζ ^ k) ^ j) =
            -(N : ℂ)⁻¹ * ∑ j ∈ Icc 1 (N - 1),
              (j : ℂ) * ((ζ ^ (N - r.val)) ^ k * (ζ ^ k) ^ j) := by
        intro k _
        simp [mul_sum, mul_left_comm]
      rw [sum_congr rfl hpt, ← mul_sum, sum_comm]
      refine congrArg _ (sum_congr rfl fun j _ => ?_)
      rw [mul_sum]
      refine sum_congr rfl fun t _ => ?_
      have : (ζ ^ (N - r.val)) ^ t * (ζ ^ t) ^ j =
          (ζ ^ (j + (N - r.val))) ^ t := by
        rw [pow_right_comm, ← pow_add, add_comm, pow_right_comm]
      rw [this]
    rw [hswap]
    have hgeom : ∀ j ∈ Icc 1 (N - 1),
        ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t =
          if j = r.val then (N - 1 : ℂ) else -1 := by
      intro j hj
      simp only [mem_Icc] at hj
      have hjlt : j < N := lt_of_le_of_lt hj.2 (Nat.sub_lt (Nat.pos_of_neZero N) (by omega))
      have hiff := dvd_add_sub_iff hN hj.1 hjlt hrpos r.isLt
      rw [sum_Icc_zeta_pow hζ hN]
      simp [hiff]
    have hr_mem : r.val ∈ Icc 1 (N - 1) := by
      simp only [mem_Icc]
      omega
    have hsumj :
        ∑ j ∈ Icc 1 (N - 1), (j : ℂ) *
            ∑ t ∈ Icc 1 (N - 1), (ζ ^ (j + (N - r.val))) ^ t =
          -∑ j ∈ Icc 1 (N - 1), (j : ℂ) + (r.val : ℂ) * N := by
      rw [sum_congr rfl fun j hj => congrArg _ (hgeom j hj)]
      exact sum_cast_mul_ite hr_mem
    rw [hsumj, sum_Icc_cast hN]
    field_simp [hN0]
    ring

lemma zeta_pow_fin_injective {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    Function.Injective (fun i : Fin N => ζ ^ i.val) := by
  intro i j h
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h)

noncomputable def fourierMatrix (N : ℕ) (ζ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  vandermonde (fun i : Fin N => ζ ^ i.val)

lemma det_fourierMatrix_ne_zero {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    (fourierMatrix N ζ).det ≠ 0 := by
  rw [fourierMatrix, det_vandermonde_ne_zero_iff]
  exact zeta_pow_fin_injective hζ

lemma zeta_pow_div {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) : ζ ^ (i - j).val = ζ ^ i.val / ζ ^ j.val := by
  rw [← zpow_int_val_sub hζ, zpow_sub₀ (zeta_ne_zero hζ), zpow_natCast, zpow_natCast]

lemma pow_mul_val_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (r i k : Fin N) :
    ζ ^ (r.val * (i - k).val) =
      ζ ^ (r.val * i.val) * ζ ^ ((-(r.val : ℤ)) * k.val) := by
  have hz := zeta_ne_zero hζ
  have hrk : ζ ^ ((-(r.val : ℤ)) * k.val) = ((ζ ^ k.val) ^ r.val)⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ hz]
    have hsum : ((k.val * r.val : ℕ) : ℤ) + ((-(r.val : ℤ)) * k.val) = 0 := by
      push_cast
      ring
    rw [hsum, zpow_zero]
  have hri : (ζ ^ i.val) ^ r.val = ζ ^ (r.val * i.val) := by
    rw [← pow_mul, mul_comm]
  calc
    ζ ^ (r.val * (i - k).val)
        = (ζ ^ (i - k).val) ^ r.val := by rw [mul_comm r.val, pow_mul]
    _ = (ζ ^ i.val / ζ ^ k.val) ^ r.val := by rw [zeta_pow_div hζ]
    _ = (ζ ^ i.val) ^ r.val / (ζ ^ k.val) ^ r.val := div_pow _ _ _
    _ = ζ ^ (r.val * i.val) * ζ ^ ((-(r.val : ℤ)) * k.val) := by
          rw [hri, hrk, div_eq_mul_inv]

lemma fin_ne_sub {N : ℕ} [NeZero N] {i k : Fin N} (hk : k ≠ 0) : i ≠ i - k := by
  intro h
  apply hk
  have h' : i - i = i - (i - k) := congrArg (fun x : Fin N => i - x) h
  rw [sub_self, sub_sub_cancel] at h'
  exact h'.symm

lemma sum_fin_offzero {N : ℕ} [NeZero N] (f : ℕ → ℂ) :
    ∑ k : Fin N, (if k = 0 then (0 : ℂ) else f k.val) = ∑ k ∈ Icc 1 (N - 1), f k := by
  have h0 : (0 : Fin N) ∈ (univ : Finset (Fin N)) := mem_univ _
  rw [← sum_erase_add (s := (univ : Finset (Fin N)))
        (f := fun k : Fin N => if k = 0 then (0 : ℂ) else f k.val) h0]
  have hzero :
      (if (0 : Fin N) = 0 then (0 : ℂ) else f (0 : Fin N).val) = 0 := if_pos rfl
  rw [hzero, add_zero]
  refine sum_bij (fun (k : Fin N) (_ : k ∈ univ.erase 0) => k.val) ?_ ?_ ?_ ?_
  · intro k hk
    have hk0 : k ≠ 0 := (mem_erase.mp hk).1
    have hkval : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    simp only [mem_Icc]
    exact ⟨Nat.pos_of_ne_zero hkval, Nat.le_pred_of_lt k.isLt⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro t ht
    simp only [mem_Icc] at ht
    have htN : t < N :=
      lt_of_le_of_lt ht.2 (Nat.sub_lt (Nat.pos_of_neZero N) Nat.zero_lt_one)
    have ht0 : t ≠ 0 := Nat.ne_zero_of_lt ht.1
    refine ⟨⟨t, htN⟩, ?_, rfl⟩
    refine mem_erase.2 ⟨?_, mem_univ _⟩
    intro h
    exact ht0 (congrArg Fin.val h)
  · intro k hk
    have hk0 : k ≠ 0 := (mem_erase.mp hk).1
    simp [hk0]

lemma calogero_mulVec {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) (r i : Fin N) :
    (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i =
      ((N : ℂ) - 1 - 2 * r.val) * ζ ^ (r.val * i.val) := by
  have hre :
      (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i =
        ∑ k : Fin N, calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val) := by
    rw [mulVec, dotProduct]
    exact (Fintype.sum_equiv (Equiv.subLeft i)
      (fun k => calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val))
      (fun j => calogero N ζ i j * ζ ^ (r.val * j.val))
      (fun k => by simp [Equiv.subLeft_apply])).symm
  rw [hre]
  have hpt : ∀ k : Fin N,
      calogero N ζ i (i - k) * ζ ^ (r.val * (i - k).val) =
        (if k = 0 then (0 : ℂ)
          else 2 * ζ ^ ((-(r.val : ℤ)) * k.val) * (1 - ζ ^ k.val)⁻¹) *
          ζ ^ (r.val * i.val) := by
    intro k
    by_cases hk0 : k = 0
    · subst hk0
      simp [calogero_apply_eq, sub_zero]
    · have hik := fin_ne_sub (i := i) hk0
      rw [calogero_apply_ne hik, pow_mul_val_sub hζ r i k]
      have hzpow : ζ ^ (i.val - (i - k).val : ℤ) = ζ ^ k.val := by
        rw [zpow_int_val_sub hζ, sub_sub_cancel]
      rw [hzpow, div_eq_mul_inv, if_neg hk0]
      ring
  rw [sum_congr rfl fun k _ => hpt k, ← sum_mul,
    sum_fin_offzero (fun k =>
      2 * ζ ^ ((-(r.val : ℤ)) * k) * (1 - ζ ^ k)⁻¹),
    calogero_kernel_sum hζ hN r]

lemma fourier_pow (N : ℕ) (ζ : ℂ) (j r : Fin N) :
    (ζ ^ j.val) ^ r.val = ζ ^ (r.val * j.val) := by
  rw [← pow_mul, mul_comm]

lemma calogero_mul_fourier {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hN : 1 < N) :
    calogero N ζ * fourierMatrix N ζ =
      fourierMatrix N ζ * diagonal fun r : Fin N => (N : ℂ) - 1 - 2 * r.val := by
  ext i r
  have hvec := calogero_mulVec hζ hN r i
  calc
    (calogero N ζ * fourierMatrix N ζ) i r
        = ∑ j, calogero N ζ i j * fourierMatrix N ζ j r := mul_apply
    _ = ∑ j, calogero N ζ i j * ζ ^ (r.val * j.val) := by
          simp [fourierMatrix, vandermonde_apply, fourier_pow]
    _ = (calogero N ζ).mulVec (fun j => ζ ^ (r.val * j.val)) i := rfl
    _ = ((N : ℂ) - 1 - 2 * r.val) * ζ ^ (r.val * i.val) := hvec
    _ = fourierMatrix N ζ i r * ((N : ℂ) - 1 - 2 * r.val) := by
          simp [fourierMatrix, vandermonde_apply, fourier_pow, mul_comm]
    _ = (fourierMatrix N ζ *
          diagonal fun t : Fin N => (N : ℂ) - 1 - 2 * t.val) i r :=
          (mul_diagonal (fun t : Fin N => (N : ℂ) - 1 - 2 * t.val)
            (fourierMatrix N ζ) i r).symm

lemma prod_odd_cast {n : ℕ} :
    ∏ k ∈ range n, (2 * k + 1 : ℂ) =
      ∏ k ∈ range n, ((2 * k + 1 : ℕ) : ℂ) := by
  refine prod_congr rfl fun k _ => ?_
  simp [Nat.cast_add, Nat.cast_mul, Nat.cast_one]

lemma prod_calogero_eigenvalues (n : ℕ) :
    ∏ r : Fin (2 * n), (((2 * n : ℕ) : ℂ) - 1 - 2 * r.val) =
      (-1 : ℂ) ^ n * a n := by
  rw [Fin.prod_univ_eq_prod_range (fun k => ((2 * n : ℕ) : ℂ) - 1 - 2 * k) (2 * n)]
  rw [show range (2 * n) = range (n + n) from by rw [two_mul]]
  rw [prod_range_add]
  have hpos :
      ∏ k ∈ range n, (((2 * n : ℕ) : ℂ) - 1 - 2 * k) =
        ∏ k ∈ range n, (2 * k + 1 : ℂ) := by
    have hcast : ∀ k ∈ range n,
        (((2 * n : ℕ) : ℂ) - 1 - 2 * k) =
          (2 : ℂ) * ((n - 1 - k : ℕ) : ℂ) + 1 := by
      intro k hk
      simp only [mem_range] at hk
      have hle : k + 1 ≤ n := Nat.succ_le_of_lt hk
      have hnk : ((n - 1 - k : ℕ) : ℂ) = (n : ℂ) - 1 - k := by
        have : n - 1 - k = n - (k + 1) := by omega
        rw [this, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
        ring
      rw [hnk, Nat.cast_mul, Nat.cast_two]
      ring
    rw [prod_congr rfl hcast]
    exact prod_range_reflect (fun k => (2 * k + 1 : ℂ)) n
  have hneg :
      ∏ k ∈ range n, (((2 * n : ℕ) : ℂ) - 1 - 2 * ((n + k : ℕ) : ℂ)) =
        (-1 : ℂ) ^ n * ∏ k ∈ range n, (2 * k + 1 : ℂ) := by
    have hpt : ∀ k ∈ range n,
        (((2 * n : ℕ) : ℂ) - 1 - 2 * ((n + k : ℕ) : ℂ)) =
          -((2 * k + 1 : ℂ)) := by
      intro k _
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
      ring
    rw [prod_congr rfl hpt, prod_neg, card_range]
  rw [hpos, hneg, prod_odd_cast, a, Nat.cast_pow, Nat.cast_prod]
  ring

lemma det_calogero {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (calogero (2 * n) ζ).det = (-1 : ℂ) ^ n * a n := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hN : 1 < 2 * n := by omega
  have hF := det_fourierMatrix_ne_zero (N := 2 * n) hζ
  have hdet := congrArg det (calogero_mul_fourier (N := 2 * n) hζ hN)
  rw [det_mul, det_mul, det_diagonal, mul_comm (fourierMatrix (2 * n) ζ).det] at hdet
  rw [← prod_calogero_eigenvalues n]
  exact mul_right_cancel₀ hF hdet

lemma prod_zpow_eq_zpow_sum {ι : Type*} [DecidableEq ι] {ζ : ℂ} (hz : ζ ≠ 0)
    (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ζ ^ f i = ζ ^ ∑ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, zpow_add₀ hz, ih]

lemma sum_val_perm {N : ℕ} (σ : Perm (Fin N)) :
    ∑ i : Fin N, ((σ i).val : ℤ) = ∑ i : Fin N, (i.val : ℤ) :=
  Fintype.sum_equiv σ (fun i : Fin N => ((σ i).val : ℤ))
    (fun i : Fin N => (i.val : ℤ)) fun _ => rfl

lemma prod_zeta_perm {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (σ : Perm (Fin N)) :
    ∏ i, ζ ^ ((σ i).val - i.val : ℤ) = 1 := by
  have hz := zeta_ne_zero hζ
  have hsum : ∑ i : Fin N, ((σ i).val - i.val : ℤ) = 0 := by
    simp [sum_sub_distrib, sum_val_perm σ]
  rw [prod_zpow_eq_zpow_sum hz (univ : Finset (Fin N))
      (fun i => ((σ i).val - i.val : ℤ)), hsum, zpow_zero]

lemma one_add_div_eq_neg_one_add_two_div {z : ℂ} (hz : 1 - z ≠ 0) :
    (1 + z) / (1 - z) = -1 + 2 / (1 - z) := by
  field_simp [hz]
  ring

lemma one_add_div_sub_one {z : ℂ} (hz : 1 - z ≠ 0) :
    (1 + z) / (1 - z) - 1 = 2 * z / (1 - z) := by
  field_simp [hz]
  ring

noncomputable def allOnes (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun _ _ => 1

lemma sunMatrix_sub_ones_diag {n : ℕ} (ζ : ℂ) (i : Fin (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)) i i = 0 := by
  simp [sunMatrix, allOnes, Matrix.sub_apply]

lemma sunMatrix_sub_ones_off {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * n))
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    (sunMatrix n ζ - allOnes (2 * n)) i j =
      2 * ζ ^ (i.val - j.val : ℤ) / (1 - ζ ^ (i.val - j.val : ℤ)) := by
  have hden := denom_ne_zero (N := 2 * n) hζ hij
  have hM := sunMatrix_apply_ne (n := n) hζ hij
  simp [allOnes, Matrix.sub_apply, hM]
  exact one_add_div_sub_one hden

lemma prod_eq_zero_of_fixed {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) {σ : Perm (Fin N)}
    (hfix : ∃ i, σ i = i) : ∏ i, M (σ i) i = 0 := by
  obtain ⟨i, hi⟩ := hfix
  exact prod_eq_zero (mem_univ i) (by simp [hi, hdiag i])

lemma permanent_of_zero_diag {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) :
    M.permanent =
      ∑ σ : Perm (Fin N),
        if (∀ i, σ i ≠ i) then ∏ i, M (σ i) i else 0 := by
  refine sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, σ i ≠ i
  · simp [h]
  · simp [h]
    exact prod_eq_zero_of_fixed M hdiag (by simpa using h)

lemma det_of_zero_diag {N : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin N) (Fin N) R) (hdiag : ∀ i, M i i = 0) :
    M.det =
      ∑ σ : Perm (Fin N),
        if (∀ i, σ i ≠ i) then (Perm.sign σ : R) * ∏ i, M (σ i) i else 0 := by
  rw [det_apply']
  refine sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, σ i ≠ i
  · simp [h]
  · have hz : ∏ i, M (σ i) i = 0 :=
      prod_eq_zero_of_fixed M hdiag (by simpa using h)
    simp [h, hz]

lemma calogero_prod_of_derangement {N : ℕ} [NeZero N] {ζ : ℂ}
    {σ : Perm (Fin N)} (hder : ∀ i, σ i ≠ i) :
    ∏ i, calogero N ζ (σ i) i =
      (2 : ℂ) ^ N * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  have hpt : ∀ i, calogero N ζ (σ i) i =
      2 * (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i
    rw [calogero_apply_ne (hder i), div_eq_mul_inv]
  simp_rw [hpt]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]

lemma det_calogero_eq_signed_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (calogero (2 * n) ζ).det =
      (2 : ℂ) ^ (2 * n) *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) then
            (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hdiag : ∀ i : Fin (2 * n), calogero (2 * n) ζ i i = 0 := fun i =>
    calogero_apply_eq _ _
  rw [det_of_zero_diag _ hdiag]
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
          (Perm.sign σ : ℂ) * ∏ i, calogero (2 * n) ζ (σ i) i
        else 0) =
        (2 : ℂ) ^ (2 * n) *
          (if (∀ i, σ i ≠ i) then
            (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · rw [calogero_prod_of_derangement (N := 2 * n) h]
      ring
    · simp
  simp_rw [hterm, ← mul_sum]

lemma sunMatrix_sub_ones_prod_of_derangement {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) {σ : Perm (Fin (2 * n))}
    (hder : ∀ i, σ i ≠ i) :
    ∏ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i =
      (2 : ℂ) ^ (2 * n) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  have hpt : ∀ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i =
      2 * ζ ^ ((σ i).val - i.val : ℤ) *
        (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i
    rw [sunMatrix_sub_ones_off hζ (hder i), div_eq_mul_inv]
  simp_rw [hpt]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
    prod_zeta_perm (N := 2 * n) hζ]
  ring

lemma permanent_sunMatrix_sub_ones {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)).permanent =
      (2 : ℂ) ^ (2 * n) *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) then
            ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have : NeZero n := ⟨by omega⟩
  have hdiag : ∀ i : Fin (2 * n), (sunMatrix n ζ - allOnes (2 * n)) i i = 0 :=
    fun i => sunMatrix_sub_ones_diag ζ i
  rw [permanent_of_zero_diag _ hdiag]
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
          ∏ i, (sunMatrix n ζ - allOnes (2 * n)) (σ i) i
        else 0) =
        (2 : ℂ) ^ (2 * n) *
          (if (∀ i, σ i ≠ i) then
            ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · exact sunMatrix_sub_ones_prod_of_derangement hζ h
    · simp
  simp_rw [hterm, ← mul_sum]

lemma signed_derangement_inv_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) then
          (Perm.sign σ : ℂ) * ∏ i, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) =
      (-1 : ℂ) ^ n * a n / (2 : ℂ) ^ (2 * n) := by
  have hdet := det_calogero hn hζ
  have hsum := det_calogero_eq_signed_sum hn hζ
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hdet] at hsum
  exact eq_div_of_mul_eq h2 (by rw [mul_comm]; exact hsum.symm)

/-- Guo–Li–Tao–Wei Lemma 3.1 weight along the support of `σ`. -/
noncomputable def cycleEdgeWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) : ℂ :=
  ∏ i ∈ σ.support, (x (σ i) - x i)⁻¹

/-- Two opposite 3-cycles cancel. This is the length-3 case of Guo Lemma 3.1. -/
lemma two_three_cycles_cancel {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    (y - x)⁻¹ * (z - y)⁻¹ * (x - z)⁻¹ +
      (z - x)⁻¹ * (y - z)⁻¹ * (x - y)⁻¹ = 0 := by
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have hzy : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  have hxz : x - z ≠ 0 := sub_ne_zero.2 hzx.symm
  have hzx' : z - x ≠ 0 := sub_ne_zero.2 hzx
  have hyz' : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hxy' : x - y ≠ 0 := sub_ne_zero.2 hxy
  field_simp [hyx, hzy, hxz, hzx', hyz', hxy']
  ring

lemma inv_sub_sub_eq {R : Type*} [Field R] (w y z : R) (hy : w ≠ y) (hz : w ≠ z) :
    (z - y) / ((w - y) * (z - w)) = (w - y)⁻¹ - (w - z)⁻¹ := by
  have h1 : w - y ≠ 0 := sub_ne_zero.2 hy
  have h2 : w - z ≠ 0 := sub_ne_zero.2 hz
  have h3 : z - w ≠ 0 := sub_ne_zero.2 hz.symm
  field_simp [h1, h2, h3]
  ring

/-- Insertion kernel along a cycle of the remaining points. The sum telescopes. -/
lemma sum_insert_kernel {m : ℕ} [NeZero m] (w : ℂ) (z : Fin m → ℂ)
    (hw : ∀ k, w ≠ z k) :
    ∑ k : Fin m, (z (k + 1) - z k) / ((w - z k) * (z (k + 1) - w)) = 0 := by
  have hterm : ∀ k, (z (k + 1) - z k) / ((w - z k) * (z (k + 1) - w)) =
      (w - z k)⁻¹ - (w - z (k + 1))⁻¹ := fun k =>
    inv_sub_sub_eq w (z k) (z (k + 1)) (hw k) (hw (k + 1))
  simp_rw [hterm]
  rw [sum_sub_distrib]
  have hperm :
      ∑ k : Fin m, (w - z (k + 1))⁻¹ = ∑ k : Fin m, (w - z k)⁻¹ :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin m))
      (fun k => (w - z (k + 1))⁻¹) (fun k => (w - z k)⁻¹) (fun _ => rfl)
  rw [hperm, sub_self]

lemma prod_toFinset_getElem {α : Type*} [DecidableEq α] {R : Type*} [CommMonoid R]
    {l : List α} (hl : l.Nodup) (g : α → R) :
    ∏ a ∈ l.toFinset, g a = ∏ i : Fin l.length, g (l[i.val]) := by
  refine (prod_bij (fun (i : Fin l.length) (_ : i ∈ univ) => l[i.val]) ?_ ?_ ?_ ?_).symm
  · intro i _
    simp
  · intro i _ j _ h
    exact Fin.ext (List.Nodup.getElem_inj_iff hl |>.mp h)
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp ha)
    exact ⟨⟨i, hi⟩, mem_univ _, rfl⟩
  · intro i _
    rfl

lemma prod_fin_eq_prod_range {n : ℕ} (f : Fin n → ℂ) :
    ∏ i, f i = ∏ i ∈ (range n).attach, f ⟨i.1, mem_range.mp i.2⟩ := by
  refine prod_bij (fun (i : Fin n) _ => ⟨i.val, mem_range.mpr i.isLt⟩) ?_ ?_ ?_ ?_
  · intro i _
    simp
  · intro i _ j _ h
    exact Fin.ext (congrArg Subtype.val h)
  · intro a _
    exact ⟨⟨a.1, mem_range.mp a.2⟩, mem_univ _, rfl⟩
  · intro i _
    rfl

lemma cycleEdgeWeight_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {l : List α} (hl : l.Nodup) (h2 : 2 ≤ l.length) :
    cycleEdgeWeight x l.formPerm =
      ∏ i : Fin l.length,
        (x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega))) - x (l[i.val]))⁻¹ := by
  have hne : ∀ a : α, l ≠ [a] := by
    intro a h
    simp [h] at h2
  rw [cycleEdgeWeight, List.support_formPerm_of_nodup l hl hne,
    prod_toFinset_getElem hl]
  refine prod_congr rfl fun i _ => ?_
  rw [List.formPerm_apply_getElem l hl i.val i.isLt]

lemma cycleEdgeWeight_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    cycleEdgeWeight x (σ * τ) = cycleEdgeWeight x σ * cycleEdgeWeight x τ := by
  simp only [cycleEdgeWeight]
  rw [h.support_mul, prod_union h.disjoint_support]
  refine congr_arg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun a ha => ?_
    have hτ : τ a = a := Equiv.Perm.notMem_support.mp (h.mem_imp ha)
    simp [hτ]
  · refine prod_congr rfl fun a ha => ?_
    have hσa : σ (τ a) = τ a := by
      have : τ a ∈ τ.support := (Equiv.Perm.apply_mem_support (f := τ)).2 ha
      exact Equiv.Perm.notMem_support.mp (h.symm.mem_imp this)
    simp [hσa]

lemma getElem_rotate_zero {α : Type*} (L : List α) {k : ℕ} (_hk : k < L.length) :
    (L.rotate k)[0]'(by simp [List.length_rotate]; omega) = L[k] := by
  simp [List.getElem_rotate, Nat.mod_eq_of_lt _hk]

lemma getElem_rotate_last {α : Type*} (L : List α) {k : ℕ}
    (h2 : 2 ≤ L.length) (_hk : k < L.length) :
    (L.rotate k)[L.length - 1]'(by simp [List.length_rotate]; omega) =
      L[(k + (L.length - 1)) % L.length]'(Nat.mod_lt _ (by omega)) := by
  have hlt : L.length - 1 < (L.rotate k).length := by
    simp [List.length_rotate]; omega
  rw [List.getElem_rotate (h := hlt), Nat.add_comm]

lemma formPerm_cons_apply_head {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hl : (p :: L).Nodup) (hLpos : 1 ≤ L.length) :
    (p :: L).formPerm p = L[0]'(by omega) := by
  have hlen : 1 < (p :: L).length := by simp; omega
  simpa using List.formPerm_apply_getElem_zero (p :: L) hl hlen

lemma getLast_cons_eq {α : Type*} {p : α} {L : List α} (hLne : L ≠ []) :
    (p :: L).getLast (List.cons_ne_nil p L) = L.getLast hLne := by
  cases L with
  | nil => contradiction
  | cons _ _ => rfl

lemma formPerm_cons_apply_getLast {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hLne : L ≠ []) :
    (p :: L).formPerm (L.getLast hLne) = p := by
  simpa [getLast_cons_eq hLne] using List.formPerm_apply_getLast p L

lemma formPerm_apply_getLast_eq_head {α : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) (hLne : L ≠ []) (h2 : 2 ≤ L.length) :
    L.formPerm (L.getLast hLne) = L[0]'(by omega) := by
  rw [List.getLast_eq_getElem, List.formPerm_apply_getElem L hL]
  have hmod : (L.length - 1 + 1) % L.length = 0 := by
    rw [Nat.sub_add_cancel (show 1 ≤ L.length by omega), Nat.mod_self]
  simp [hmod]

lemma formPerm_cons_apply_of_ne_getLast {α : Type*} [DecidableEq α] {p : α} {L : List α}
    (hl : (p :: L).Nodup) (hL : L.Nodup) (hLne : L ≠ []) {a : α}
    (ha : a ∈ L) (ha_ne : a ≠ L.getLast hLne) :
    (p :: L).formPerm a = L.formPerm a := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk1 : k + 1 < L.length := by
    have hk_ne : k ≠ L.length - 1 := by
      intro hke
      apply ha_ne
      rw [List.getLast_eq_getElem]
      subst hke
      rfl
    omega
  have hidx : L[k] = (p :: L)[k + 1]'(by simp; omega) :=
    (List.getElem_cons_succ p L k (by simp; omega)).symm
  rw [List.formPerm_apply_lt_getElem L hL k hk1, hidx,
    List.formPerm_apply_lt_getElem (p :: L) hl (k + 1) (by simp; omega)]
  exact (List.getElem_cons_succ p L (k + 1) (by simp; omega)).symm

/-- Inserting `p` on one edge of the `L`-cycle multiplies the remaining-cycle weight
by the insertion kernel. -/
lemma cycleEdgeWeight_formPerm_cons {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    cycleEdgeWeight x (List.formPerm (p :: L)) =
      cycleEdgeWeight x L.formPerm *
        (x (L[0]'(by omega)) - x (L[L.length - 1]'(by omega))) *
        (x (L[0]'(by omega)) - x p)⁻¹ *
        (x p - x (L[L.length - 1]'(by omega)))⁻¹ := by
  have hl : (p :: L).Nodup := List.nodup_cons.2 ⟨hp, hL⟩
  have hLne : L ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hneG : ∀ a : α, p :: L ≠ [a] := by
    cases L with
    | nil => intro a _; simp at h2
    | cons _ _ => intro a h; simp at h
  have hneL : ∀ a : α, L ≠ [a] := by
    intro a h
    have hlenL : L.length = 1 := by simp [h]
    omega
  unfold cycleEdgeWeight
  rw [List.support_formPerm_of_nodup _ hl hneG,
    List.support_formPerm_of_nodup _ hL hneL, List.toFinset_cons]
  have hp' : p ∉ L.toFinset := by simpa using hp
  rw [prod_insert hp', formPerm_cons_apply_head hl (by omega)]
  have hlast_mem : L.getLast hLne ∈ L.toFinset :=
    List.mem_toFinset.2 (List.getLast_mem hLne)
  rw [← prod_erase_mul L.toFinset _ hlast_mem]
  have hagree :
      ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x ((p :: L).formPerm a) - x a)⁻¹ =
        ∏ a ∈ L.toFinset.erase (L.getLast hLne),
          (x (L.formPerm a) - x a)⁻¹ :=
    prod_congr rfl fun a ha => by
      rw [formPerm_cons_apply_of_ne_getLast hl hL hLne
        (List.mem_toFinset.mp (mem_of_mem_erase ha)) (ne_of_mem_erase ha)]
  rw [hagree, formPerm_cons_apply_getLast hLne]
  have hLsplit :
      (∏ i ∈ L.toFinset, (x (L.formPerm i) - x i)⁻¹) =
        (∏ a ∈ L.toFinset.erase (L.getLast hLne), (x (L.formPerm a) - x a)⁻¹) *
          (x (L.formPerm (L.getLast hLne)) - x (L.getLast hLne))⁻¹ :=
    (prod_erase_mul L.toFinset (fun i => (x (L.formPerm i) - x i)⁻¹) hlast_mem).symm
  rw [hLsplit, formPerm_apply_getLast_eq_head hL hLne h2]
  have hlast_get : L.getLast hLne = L[L.length - 1]'(by omega) := List.getLast_eq_getElem _
  rw [hlast_get]
  have hx0p : x (L[0]'(by omega)) ≠ x p :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp)
  have hxpLast : x p ≠ x (L[L.length - 1]'(by omega)) :=
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp).symm
  have hxends : x (L[0]'(by omega)) ≠ x (L[L.length - 1]'(by omega)) := by
    refine hx.ne ?_
    exact (List.Nodup.getElem_inj_iff hL).not.mpr (by omega)
  have hne1 : x (L[0]'(by omega)) - x (L[L.length - 1]'(by omega)) ≠ 0 :=
    sub_ne_zero.2 hxends
  have hne2 : x (L[0]'(by omega)) - x p ≠ 0 := sub_ne_zero.2 hx0p
  have hne3 : x p - x (L[L.length - 1]'(by omega)) ≠ 0 := sub_ne_zero.2 hxpLast
  field_simp [hne1, hne2, hne3]

/-- Guo Lemma 3.1 class sum: rotating the tail after a fixed point sums to zero. -/
lemma sum_cycleEdgeWeight_cons_rotate {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {p : α} {L : List α}
    (hL : L.Nodup) (hp : p ∉ L) (h2 : 2 ≤ L.length)
    (hx : Function.Injective x) :
    ∑ k : Fin L.length, cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)) = 0 := by
  have : NeZero L.length := ⟨by omega⟩
  have hμ :
      ∀ k : Fin L.length,
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)) =
          cycleEdgeWeight x L.formPerm *
            (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) -
              x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega))) *
            (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) - x p)⁻¹ *
            (x p - x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega)))⁻¹ := by
    intro k
    have hrot : (L.rotate k.val).Nodup := (List.nodup_rotate).2 hL
    have hp' : p ∉ L.rotate k.val := by
      simpa [List.mem_rotate] using hp
    have h2' : 2 ≤ (L.rotate k.val).length := by simpa [List.length_rotate] using h2
    have hcons := cycleEdgeWeight_formPerm_cons (x := x) hrot hp' h2' hx
    rw [List.formPerm_rotate L hL k.val] at hcons
    simpa [List.length_rotate] using hcons
  simp_rw [hμ, mul_assoc]
  rw [← mul_sum]
  convert mul_zero (cycleEdgeWeight x L.formPerm)
  let z : Fin L.length → ℂ := fun i => x (L[i.val])
  have hw : ∀ k : Fin L.length, x p ≠ z k := fun k =>
    hx.ne (ne_of_mem_of_not_mem (List.getElem_mem _) hp).symm
  let extra : Fin L.length → ℂ := fun k =>
    (x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) -
      x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega))) *
      ((x ((L.rotate k.val)[0]'(by simp [List.length_rotate]; omega)) - x p)⁻¹ *
        (x p - x ((L.rotate k.val)[L.length - 1]'(by simp [List.length_rotate]; omega)))⁻¹)
  show ∑ k, extra k = 0
  have hidx : ∀ k : Fin L.length,
      ((k + 1).val + (L.length - 1)) % L.length = k.val := by
    intro k
    have npos : 0 < L.length := by omega
    have hk1 : (k + 1).val = (k.val + 1) % L.length := by simp [Fin.val_add]
    rw [hk1]
    calc ((k.val + 1) % L.length + (L.length - 1)) % L.length
        = (k.val + 1 + (L.length - 1)) % L.length := Nat.mod_add_mod _ _ _
      _ = (k.val + L.length) % L.length := by
          have : 1 + (L.length - 1) = L.length := by omega
          rw [Nat.add_assoc, this]
      _ = k.val := by
          rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt k.isLt]
  have hshift : ∀ k : Fin L.length,
      extra (k + 1) =
        (z (k + 1) - z k) / ((x p - z k) * (z (k + 1) - x p)) := by
    intro k
    have h0 := getElem_rotate_zero L (k + 1).isLt
    have hlast := getElem_rotate_last L h2 (k + 1).isLt
    have hidxk : ((k + 1).val + (L.length - 1)) % L.length = k.val := hidx k
    have hne1 : z (k + 1) - x p ≠ 0 := sub_ne_zero.2 (hw (k + 1)).symm
    have hne2 : x p - z k ≠ 0 := sub_ne_zero.2 (hw k)
    simp only [extra, h0, hlast, hidxk, z] at hne1 hne2 ⊢
    field_simp [hne1, hne2]
  have hreindex : ∑ k, extra (k + 1) = ∑ k, extra k :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin L.length))
      (fun k => extra (k + 1)) extra (fun _ => rfl)
  have hker :
      ∑ k, extra (k + 1) =
        ∑ k, (z (k + 1) - z k) / ((x p - z k) * (z (k + 1) - x p)) :=
    sum_congr rfl fun k _ => hshift k
  rw [← hreindex, hker]
  exact sum_insert_kernel (x p) z hw

lemma ofFn_rotate {α : Type*} {m : ℕ} [NeZero m] (f : Fin m → α) (k : Fin m) :
    (List.ofFn f).rotate k.val = List.ofFn fun i => f (i + k) := by
  refine List.ext_getElem (by simp [List.length_rotate, List.length_ofFn]) ?_
  intro i hi _hi'
  have him : i < m := by simp [List.length_ofFn] at hi; exact hi
  rw [List.getElem_rotate]
  simp only [List.getElem_ofFn, List.length_ofFn]
  refine congr_arg f ?_
  ext
  simp [Fin.val_add]

/-- Guo Lemma 3.1: the sum of insertion weights over all listings of the remaining
points is zero when at least two remaining points are present. -/
lemma sum_cycleEdgeWeight_ncycles {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) (p : α)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ∑ e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p},
      cycleEdgeWeight x (List.formPerm (p :: List.ofFn fun i => (e i).1)) = 0 := by
  set m := Fintype.card {q : α // q ≠ p}
  have : NeZero m := ⟨by omega⟩
  have hclass :
      ∀ e : Fin m ≃ {q : α // q ≠ p},
        ∑ k : Fin m,
            cycleEdgeWeight x
              (List.formPerm
                (p :: (List.ofFn fun i => (e i).1).rotate k.val)) = 0 := by
    intro e
    let L := List.ofFn fun i => (e i).1
    have hL : L.Nodup :=
      List.nodup_ofFn_ofInjective fun i j hij => e.injective (Subtype.ext hij)
    have hpL : p ∉ L := by
      intro hmem
      rw [List.mem_ofFn'] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact (e i).2 hi
    have h2 : 2 ≤ L.length := by
      simpa [L, List.length_ofFn] using hcard
    have hsum := sum_cycleEdgeWeight_cons_rotate (x := x) hL hpL h2 hx
    have hlen : L.length = m := List.length_ofFn
    refine Eq.trans ?_ hsum
    refine Fintype.sum_equiv (finCongr hlen.symm)
      (fun k : Fin m =>
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)))
      (fun k : Fin L.length =>
        cycleEdgeWeight x (List.formPerm (p :: L.rotate k.val)))
      (fun _ => rfl)
  let W : (Fin m ≃ {q : α // q ≠ p}) → ℂ :=
    fun σ => cycleEdgeWeight x (List.formPerm (p :: List.ofFn fun i : Fin m => (σ i).1))
  have hrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        (List.ofFn fun i => (e i).1).rotate k.val =
          List.ofFn fun i : Fin m => (e (i + k)).1 := fun e k => ofFn_rotate _ k
  have hWrot :
      ∀ (e : Fin m ≃ {q : α // q ≠ p}) (k : Fin m),
        cycleEdgeWeight x
            (List.formPerm (p :: (List.ofFn fun i => (e i).1).rotate k.val)) =
          W ((Equiv.addRight k).trans e) := by
    intro e k
    rw [hrot]
    rfl
  have hdouble :
      ∑ e : Fin m ≃ {q : α // q ≠ p}, ∑ k : Fin m, W ((Equiv.addRight k).trans e) = 0 := by
    simp_rw [← hWrot]
    rw [sum_congr rfl fun e _ => hclass e]
    simp
  have hreindex :
      ∀ k : Fin m,
        ∑ e : Fin m ≃ {q : α // q ≠ p}, W ((Equiv.addRight k).trans e) =
          ∑ e, W e := by
    intro k
    let φ :=
      (Equiv.addRight k).symm.equivCongr (Equiv.refl {q : α // q ≠ p})
    have hφ : ∀ e, φ e = (Equiv.addRight k).trans e := by
      intro e
      ext i
      dsimp [φ]
    simp_rw [← hφ]
    exact Equiv.sum_comp φ W
  rw [sum_comm] at hdouble
  simp_rw [hreindex] at hdouble
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hdouble
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact (mul_eq_zero.mp hdouble).resolve_left hm0

lemma zeta_pow_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ j.val - ζ ^ i.val =
      - (ζ ^ i.val) * (1 - ζ ^ (j.val - i.val : ℤ)) := by
  have hz := zeta_ne_zero hζ
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ hz
  have hdiv : ζ ^ j.val / ζ ^ i.val = ζ ^ (j.val - i.val : ℤ) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
  have hsplit : ζ ^ j.val - ζ ^ i.val = ζ ^ i.val * (ζ ^ j.val / ζ ^ i.val - 1) := by
    field_simp [hi]
  rw [hsplit, hdiv]
  ring

lemma cycleEdgeWeight_zeta {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (σ : Perm (Fin N)) :
    cycleEdgeWeight (fun i => ζ ^ i.val) σ =
      (∏ i ∈ σ.support, (-ζ ^ i.val)⁻¹) *
        ∏ i ∈ σ.support, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  unfold cycleEdgeWeight
  have hterm : ∀ i ∈ σ.support,
      (ζ ^ (σ i).val - ζ ^ i.val)⁻¹ =
        (-ζ ^ i.val)⁻¹ * (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
    intro i hi
    have hij : σ i ≠ i := Equiv.Perm.mem_support.mp hi
    have hζi : ζ ^ i.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero hζ)
    have hne : 1 - ζ ^ ((σ i).val - i.val : ℤ) ≠ 0 := denom_ne_zero hζ hij
    rw [zeta_pow_sub hζ]
    field_simp [hζi, hne]
  simp_rw [← prod_mul_distrib]
  refine prod_congr rfl hterm

lemma card_subtype_ne {α : Type*} [Fintype α] [DecidableEq α] (p : α) :
    Fintype.card {q : α // q ≠ p} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne', card_erase_of_mem (mem_univ p), card_univ]

lemma listing_nodup {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) :
    (p :: List.ofFn fun i => (e i).1).Nodup := by
  refine List.nodup_cons.2 ⟨?_, List.nodup_ofFn_ofInjective fun i j hij =>
    e.injective (Subtype.ext hij)⟩
  intro hmem
  rw [List.mem_ofFn'] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact (e i).2 hi

lemma listing_isCycle {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (List.formPerm (p :: List.ofFn fun i => (e i).1)).IsCycle := by
  refine List.isCycle_formPerm (listing_nodup e) ?_
  simpa [List.length_cons, List.length_ofFn] using
    (Nat.le_add_right_of_le hcard : 2 ≤ Fintype.card {q : α // q ≠ p} + 1)

lemma listing_support_univ {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (List.formPerm (p :: List.ofFn fun i => (e i).1)).support = (univ : Finset α) := by
  have hne : ∀ a : α, p :: List.ofFn (fun i => (e i).1) ≠ [a] := by
    intro a h
    have hlen := congr_arg List.length h
    simp only [List.length_cons, List.length_ofFn, List.length_nil] at hlen
    omega
  rw [List.support_formPerm_of_nodup _ (listing_nodup e) hne, List.toFinset_cons]
  ext q
  simp only [mem_insert, List.mem_toFinset, mem_univ, iff_true]
  by_cases hqp : q = p
  · exact Or.inl hqp
  · refine Or.inr ?_
    rw [List.mem_ofFn']
    refine ⟨e.symm ⟨q, hqp⟩, ?_⟩
    simp

/-- Cycle determined by a listing of the remaining points after a fixed `p`. -/
noncomputable def listingPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) : Perm α :=
  List.formPerm (p :: List.ofFn fun i => (e i).1)

lemma listingPerm_eq_formPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) :
    listingPerm e = List.formPerm (p :: List.ofFn fun i => (e i).1) :=
  rfl

lemma listingPerm_isCycle {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (listingPerm e).IsCycle := by
  delta listingPerm
  exact listing_isCycle e hcard

lemma listingPerm_support_univ {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (listingPerm e).support = (univ : Finset α) := by
  delta listingPerm
  exact listing_support_univ e hcard

lemma derangement_support_univ {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : ∀ i, σ i ≠ i) : σ.support = univ := by
  ext i
  simp [Equiv.Perm.mem_support, h]

lemma cycleEdgeWeight_zeta_univ {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {σ : Perm (Fin N)} (hsup : σ.support = univ) :
    cycleEdgeWeight (fun i => ζ ^ i.val) σ =
      (∏ i : Fin N, (-ζ ^ i.val)⁻¹) *
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ := by
  rw [cycleEdgeWeight_zeta hζ, hsup]

lemma zeta_inv_prod_ne_zero {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    (∏ i : Fin N, (-ζ ^ i.val)⁻¹) ≠ 0 :=
  prod_ne_zero_iff.2 fun i _ =>
    inv_ne_zero (neg_ne_zero.2 (pow_ne_zero i.val (zeta_ne_zero hζ)))

lemma listing_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (p : Fin N)
    (hcard : 2 ≤ Fintype.card {q : Fin N // q ≠ p}) :
    ∑ e : Fin (Fintype.card {q : Fin N // q ≠ p}) ≃ {q : Fin N // q ≠ p},
      ∏ i : Fin N, (1 - ζ ^ (((listingPerm e) i).val - i.val : ℤ))⁻¹ = 0 := by
  have hsum := sum_cycleEdgeWeight_ncycles (fun i => ζ ^ i.val)
    (zeta_pow_fin_injective hζ) p hcard
  have hterm : ∀ e,
      cycleEdgeWeight (fun i => ζ ^ i.val)
          (List.formPerm (p :: List.ofFn fun i => (e i).1)) =
        (∏ i : Fin N, (-ζ ^ i.val)⁻¹) *
          ∏ i : Fin N, (1 - ζ ^ (((listingPerm e) i).val - i.val : ℤ))⁻¹ := fun e => by
    have hsup := listingPerm_support_univ e hcard
    have := cycleEdgeWeight_zeta_univ hζ hsup
    exact this
  simp_rw [hterm] at hsum
  rw [← mul_sum] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (zeta_inv_prod_ne_zero hζ)

lemma isCycle_univ_ne {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hsup : σ.support = univ) (p : α) : σ p ≠ p :=
  Equiv.Perm.mem_support.mp (by rw [hsup]; exact mem_univ p)

lemma orderOf_isCycle_univ {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    orderOf σ = Fintype.card α := by
  rw [hσ.orderOf, hsup, card_univ]

lemma card_subtype_ne_lt_card {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (i : Fin (Fintype.card {q : α // q ≠ p})) :
    i.val + 1 < Fintype.card α := by
  have hle : i.val + 1 ≤ Fintype.card {q : α // q ≠ p} := Nat.succ_le_of_lt i.isLt
  have hcard := card_subtype_ne p
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨p⟩
  omega

lemma isCycle_pow_succ_ne {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) (p : α)
    (i : Fin (Fintype.card {q : α // q ≠ p})) :
    (σ ^ (i.val + 1)) p ≠ p := by
  have hp := isCycle_univ_ne hsup p
  intro h
  have h1 : σ ^ (i.val + 1) = 1 := (hσ.pow_eq_one_iff' hp).2 h
  have hdvd : orderOf σ ∣ i.val + 1 := orderOf_dvd_iff_pow_eq_one.2 h1
  have hlt : i.val + 1 < orderOf σ := by
    rw [orderOf_isCycle_univ hσ hsup]
    exact card_subtype_ne_lt_card p i
  exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hlt hdvd

noncomputable def ncycleToListingFun {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ)
    (i : Fin (Fintype.card {q : α // q ≠ p})) : {q : α // q ≠ p} :=
  ⟨(σ ^ (i.val + 1)) p, isCycle_pow_succ_ne hσ hsup p i⟩

lemma ncycleToListingFun_injective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Function.Injective (ncycleToListingFun (p := p) hσ hsup) := by
  intro i j hij
  have hij' : (σ ^ (i.val + 1)) p = (σ ^ (j.val + 1)) p :=
    congrArg Subtype.val hij
  have hp := isCycle_univ_ne hsup p
  have heq : σ ^ (i.val + 1) = σ ^ (j.val + 1) :=
    (hσ.pow_eq_pow_iff).2 ⟨p, hp, hij'⟩
  have hmod := pow_inj_mod.mp heq
  have hlt : ∀ k : Fin (Fintype.card {q : α // q ≠ p}),
      k.val + 1 < orderOf σ := fun k => by
    rw [orderOf_isCycle_univ hσ hsup]
    exact card_subtype_ne_lt_card p k
  rw [Nat.mod_eq_of_lt (hlt i), Nat.mod_eq_of_lt (hlt j)] at hmod
  exact Fin.ext (Nat.succ_injective hmod)

lemma ncycleToListingFun_surjective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Function.Surjective (ncycleToListingFun (p := p) hσ hsup) := by
  intro q
  have hp := isCycle_univ_ne hsup p
  have hq := isCycle_univ_ne hsup q.1
  have hsc : Equiv.Perm.SameCycle σ p q.1 :=
    ((Equiv.Perm.isCycle_iff_sameCycle hp).1 hσ).mpr hq
  obtain ⟨k, hklt, hk⟩ := Equiv.Perm.SameCycle.exists_pow_eq' hsc
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Perm.one_apply] at hk
    exact q.2 hk.symm
  have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hord := orderOf_isCycle_univ hσ hsup
  have hi : k - 1 < Fintype.card {q : α // q ≠ p} := by
    rw [card_subtype_ne, ← hord]
    omega
  refine ⟨⟨k - 1, hi⟩, ?_⟩
  apply Subtype.ext
  change (σ ^ (k - 1 + 1)) p = q.1
  rw [Nat.sub_add_cancel hkpos, hk]

noncomputable def ncycleToListing {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p} :=
  Equiv.ofBijective (ncycleToListingFun (p := p) hσ hsup)
    ⟨ncycleToListingFun_injective hσ hsup, ncycleToListingFun_surjective hσ hsup⟩

lemma ncycleToListing_apply {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ)
    (i : Fin (Fintype.card {q : α // q ≠ p})) :
    (ncycleToListing (p := p) hσ hsup i).1 = (σ ^ (i.val + 1)) p :=
  rfl

lemma toList_eq_cons_ofFn {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) (p : α) :
    Equiv.Perm.toList σ p =
      p :: List.ofFn fun i : Fin (Fintype.card {q : α // q ≠ p}) =>
        (σ ^ (i.val + 1)) p := by
  have hp := isCycle_univ_ne hsup p
  have hlen : (Equiv.Perm.toList σ p).length = Fintype.card α := by
    rw [Equiv.Perm.length_toList, hσ.cycleOf_eq hp, hsup, card_univ]
  refine List.ext_getElem ?_ ?_
  · have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨p⟩
    rw [hlen, List.length_cons, List.length_ofFn, card_subtype_ne]
    omega
  · intro n hn _hn'
    rw [Equiv.Perm.getElem_toList]
    cases n with
    | zero =>
      simp [pow_zero]
    | succ k =>
      simp [List.getElem_ofFn]

lemma ncycleToListing_listingPerm {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (e : Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    ncycleToListing (listingPerm_isCycle e hcard) (listingPerm_support_univ e hcard) = e := by
  ext i
  rw [ncycleToListing_apply]
  have hnodup := listing_nodup (p := p) e
  have hlt' : i.val + 1 < Fintype.card {q : α // q ≠ p} + 1 := Nat.succ_lt_succ i.isLt
  have hpow := List.formPerm_pow_apply_head p (List.ofFn fun j => (e j).1) hnodup (i.val + 1)
  delta listingPerm
  rw [hpow]
  simp only [List.length_cons, List.length_ofFn, Nat.mod_eq_of_lt hlt',
    List.getElem_cons_succ, List.getElem_ofFn]

lemma listingPerm_ncycleToListing {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    {σ : Perm α} (hσ : σ.IsCycle) (hsup : σ.support = univ) :
    listingPerm (ncycleToListing (p := p) hσ hsup) = σ := by
  have hp := isCycle_univ_ne hsup p
  have hlist :
      (p :: List.ofFn fun i : Fin (Fintype.card {q : α // q ≠ p}) =>
          (ncycleToListing (p := p) hσ hsup i).1) =
        Equiv.Perm.toList σ p := by
    simp_rw [ncycleToListing_apply]
    exact (toList_eq_cons_ofFn hσ hsup p).symm
  delta listingPerm
  rw [hlist, Equiv.Perm.formPerm_toList, hσ.cycleOf_eq hp]

noncomputable def listingEquiv {α : Type*} [Fintype α] [DecidableEq α] (p : α)
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    (Fin (Fintype.card {q : α // q ≠ p}) ≃ {q : α // q ≠ p}) ≃
      {σ : Perm α // σ.IsCycle ∧ σ.support = univ} where
  toFun e := ⟨listingPerm e, listingPerm_isCycle e hcard, listingPerm_support_univ e hcard⟩
  invFun σ := ncycleToListing σ.2.1 σ.2.2
  left_inv e := ncycleToListing_listingPerm e hcard
  right_inv σ := Subtype.ext (listingPerm_ncycleToListing σ.2.1 σ.2.2)

open scoped Classical in
lemma ncycle_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (p : Fin N)
    (hcard : 2 ≤ Fintype.card {q : Fin N // q ≠ p}) :
    ∑ σ : {σ : Perm (Fin N) // σ.IsCycle ∧ σ.support = univ},
      ∏ i : Fin N, (1 - ζ ^ ((σ.1 i).val - i.val : ℤ))⁻¹ = 0 := by
  rw [← Equiv.sum_comp (listingEquiv p hcard)
    (fun σ => ∏ i : Fin N, (1 - ζ ^ ((σ.1 i).val - i.val : ℤ))⁻¹)]
  dsimp only [listingEquiv]
  exact listing_inv_one_sub_sum hζ p hcard

lemma cycleEdgeWeight_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → Prop} [DecidablePred p] (x : α → ℂ) (u : Perm (Subtype p)) :
    cycleEdgeWeight x (Equiv.Perm.ofSubtype u) =
      cycleEdgeWeight (fun q : Subtype p => x q.1) u := by
  simp only [cycleEdgeWeight, Equiv.Perm.support_ofSubtype]
  rw [prod_map]
  refine prod_congr rfl fun q _ => ?_
  simp [Equiv.Perm.ofSubtype_apply_coe]

lemma ofSubtype_isCycle {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    {u : Perm (Subtype p)} (hu : u.IsCycle) :
    (Equiv.Perm.ofSubtype u).IsCycle :=
  hu.extendDomain (Equiv.refl _)

lemma support_ofSubtype_subset {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) :
    (Equiv.Perm.ofSubtype u).support ⊆ s := by
  intro x hx
  obtain ⟨hx', _⟩ := (Equiv.Perm.mem_support_ofSubtype x u).mp hx
  exact hx'

lemma ofSubtype_disjoint_of_support_subset_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype u) τ := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  exact Finset.disjoint_of_subset_left (support_ofSubtype_subset u)
    (Finset.disjoint_of_subset_right hτ disjoint_compl_right)

lemma two_le_card_subtype_ne_of_three {α : Type*} [Fintype α] [DecidableEq α] (p : α)
    (h : 3 ≤ Fintype.card α) :
    2 ≤ Fintype.card {q : α // q ≠ p} := by
  rw [card_subtype_ne]
  omega

lemma sum_cycleEdgeWeight_replace_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (hx : Function.Injective x) {s : Finset α}
    (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
      cycleEdgeWeight x (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = 0 := by
  have hterm : ∀ e,
      cycleEdgeWeight x (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) =
        cycleEdgeWeight (fun q : {a // a ∈ s} => x q.1) (listingPerm (p := p) e) *
          cycleEdgeWeight x τ := fun e => by
    rw [cycleEdgeWeight_mul_disjoint x
        (ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ)]
    refine congr_arg (· * cycleEdgeWeight x τ) ?_
    convert cycleEdgeWeight_ofSubtype x (listingPerm (p := p) e)
  simp_rw [hterm]
  rw [← sum_mul]
  have h0 :
      ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
        cycleEdgeWeight (fun q : {a // a ∈ s} => x q.1) (listingPerm (p := p) e) = 0 := by
    refine (sum_congr rfl fun e _ =>
      congrArg _ (listingPerm_eq_formPerm (p := p) e)).trans ?_
    exact sum_cycleEdgeWeight_ncycles (fun q : {a // a ∈ s} => x q.1)
      (hx.comp Subtype.val_injective) p hcard
  rw [h0, zero_mul]

lemma coe_units_neg_one_pow (k : ℕ) :
    ((↑((-1 : ℤˣ) ^ k) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rw [Units.val_pow_eq_pow_val]
  simp

lemma sign_of_cycleType_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (h : σ.cycleType = Multiset.replicate n 2) :
    (Perm.sign σ : ℂ) = (-1 : ℂ) ^ n := by
  rw [Equiv.Perm.sign_of_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate,
    nsmul_eq_mul]
  exact (coe_units_neg_one_pow (n * 2 + n)).trans (by
    rw [pow_add, mul_comm n 2, pow_mul, neg_one_sq, one_pow, one_mul])

lemma cycleType_eq_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (hsup : σ.support = univ) (h2 : ∀ m ∈ σ.cycleType, m = 2) :
    σ.cycleType = Multiset.replicate n 2 := by
  have hr : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 h2
  have hsum : σ.cycleType.sum = 2 * n := by
    rw [Equiv.Perm.sum_cycleType, hsup, card_univ, Fintype.card_fin]
  have hcard : Multiset.card σ.cycleType * 2 = 2 * n := by
    rw [← Nat.nsmul_eq_mul, ← Multiset.sum_replicate, ← hr, hsum]
  have hn : Multiset.card σ.cycleType = n := by omega
  rw [hr, hn]

lemma derangement_long_cycle_or_replicate_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (hsup : σ.support = univ) :
    (∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card) ∨
      σ.cycleType = Multiset.replicate n 2 := by
  by_cases hlong : ∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card
  · exact Or.inl hlong
  · refine Or.inr (cycleType_eq_replicate_two hsup ?_)
    intro m hm
    have hm2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
    have hm3 : ¬ 3 ≤ m := by
      intro h3
      rw [Equiv.Perm.cycleType_def] at hm
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hm
      exact hlong ⟨c, Finset.mem_def.mpr hc, h3⟩
    omega

lemma inv_one_sub_prod_of_univ {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {σ : Perm (Fin N)} (hsup : σ.support = univ) :
    ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹ =
      (∏ i : Fin N, (-ζ ^ i.val)⁻¹)⁻¹ *
        cycleEdgeWeight (fun i => ζ ^ i.val) σ := by
  have hC := zeta_inv_prod_ne_zero hζ
  rw [eq_inv_mul_iff_mul_eq₀ hC]
  exact (cycleEdgeWeight_zeta_univ hζ hsup).symm

lemma involution_unsigned_eq_neg_signed {n : ℕ} {ζ : ℂ} :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      (-1 : ℂ) ^ n *
        ∑ σ : Perm (Fin (2 * n)),
          if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0 := by
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (-1 : ℂ) ^ n *
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · have hsign := sign_of_cycleType_replicate_two h.2
      rw [hsign, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    · rw [mul_zero]
  simp_rw [hterm, ← mul_sum]

lemma mem_of_support_subset {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    {f : Perm α} (h : f.support ⊆ s) (x : α) : x ∈ s ↔ f x ∈ s := by
  constructor
  · intro hx
    by_cases hsup : x ∈ f.support
    · exact h (Equiv.Perm.apply_mem_support.mpr hsup)
    · rwa [Equiv.Perm.notMem_support.mp hsup]
  · intro hx
    by_cases hsup : x ∈ f.support
    · exact h hsup
    · rwa [← Equiv.Perm.notMem_support.mp hsup]

lemma ofSubtype_subtypePerm_of_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {f : Perm α} (hsub : f.support ⊆ s) :
    Equiv.Perm.ofSubtype
      (f.subtypePerm fun x => (mem_of_support_subset (s := s) hsub x).symm) = f := by
  ext x
  by_cases hx : x ∈ s
  · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx, Equiv.Perm.subtypePerm_apply]
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
    exact (Equiv.Perm.notMem_support.mp fun h => hx (hsub h)).symm

lemma two_le_card_subtype_ne_of_card_three {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (p : {a // a ∈ s}) (hs : 3 ≤ s.card) :
    2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} := by
  rw [card_subtype_ne, Fintype.card_coe]
  omega

lemma listingPerm_apply_ne {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (q : {a // a ∈ s}) : listingPerm (p := p) e q ≠ q := by
  have hsup := listingPerm_support_univ (p := p) e hcard
  have hmem : q ∈ (listingPerm (p := p) e).support := by
    rw [hsup]
    exact mem_univ q
  exact Equiv.Perm.mem_support.mp hmem

lemma support_ofSubtype_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p}) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e)).support = s := by
  ext x
  constructor
  · intro hx
    by_cases hx' : x ∈ s
    · exact hx'
    · have hne := Equiv.Perm.mem_support.mp hx
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx'] at hne
      exact (hne rfl).elim
  · intro hx
    refine Equiv.Perm.mem_support.mpr ?_
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    intro h
    exact listingPerm_apply_ne p e hcard ⟨x, hx⟩ (Subtype.ext h)

lemma support_mul_listing_τ {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support = sᶜ) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).support = univ := by
  have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e)
    (show τ.support ⊆ sᶜ from hτ.symm ▸ Subset.rfl)
  rw [Equiv.Perm.Disjoint.support_mul hd, support_ofSubtype_listing p e hcard, hτ, union_compl]

lemma inv_one_sub_replace_cycle {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {s : Finset (Fin N)} (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm (Fin N)} (hτ : τ.support = sᶜ) :
    ∑ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p},
      ∏ i : Fin N,
        (1 - ζ ^ (((Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i).val
          - i.val : ℤ))⁻¹ = 0 := by
  have hterm : ∀ e,
      (∏ i : Fin N,
          (1 - ζ ^ (((Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i).val
            - i.val : ℤ))⁻¹) =
        (∏ i : Fin N, (-ζ ^ i.val)⁻¹)⁻¹ *
          cycleEdgeWeight (fun i => ζ ^ i.val)
            (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) := fun e =>
    inv_one_sub_prod_of_univ hζ (support_mul_listing_τ p e hcard hτ)
  simp_rw [hterm]
  rw [← mul_sum, sum_cycleEdgeWeight_replace_cycle (fun i => ζ ^ i.val)
      (zeta_pow_fin_injective hζ) p hcard (show τ.support ⊆ sᶜ from hτ.symm ▸ Subset.rfl),
    mul_zero]

/-- Points that lie on a cycle of length at least 3. -/
noncomputable def longPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    Finset α :=
  univ.filter fun a => 3 ≤ (σ.cycleOf a).support.card

lemma mem_longPoints {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} {a : α} :
    a ∈ longPoints σ ↔ 3 ≤ (σ.cycleOf a).support.card := by
  simp [longPoints]

lemma longPoints_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    (longPoints σ).Nonempty ↔ ∃ c ∈ σ.cycleFactorsFinset, 3 ≤ c.support.card := by
  constructor
  · intro ⟨a, ha⟩
    rw [mem_longPoints] at ha
    have hne : σ a ≠ a := by
      intro h
      have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
      have h0 : (σ.cycleOf a).support.card = 0 := by
        rw [h1, Equiv.Perm.support_one, card_empty]
      omega
    exact ⟨σ.cycleOf a, (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
      (Equiv.Perm.mem_support.mpr hne), ha⟩
  · intro ⟨c, hc, h3⟩
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    refine ⟨a, mem_longPoints.mpr ?_⟩
    rwa [← Equiv.Perm.cycle_is_cycleOf ha hc]

lemma inv_apply_eq_self_of_apply_eq_self {α : Type*} {c : Perm α} {x : α}
    (h : c x = x) : c⁻¹ x = x := by
  refine c.injective ?_
  have hleft : c (c⁻¹ x) = x := by simp
  rw [hleft, h]

lemma remainder_apply_eq_self_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {x : α} (hx : x ∈ c.support) :
    (σ * c⁻¹) x = x := by
  have hagree := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  have hxinv : c⁻¹ x ∈ c.support := by
    have hx' : x ∈ c⁻¹.support := by rwa [Equiv.Perm.support_inv]
    have hx'' : c⁻¹ x ∈ c⁻¹.support := Equiv.Perm.apply_mem_support.mpr hx'
    rwa [Equiv.Perm.support_inv] at hx''
  change σ (c⁻¹ x) = x
  rw [← hagree _ hxinv]
  simp

lemma remainder_support_eq_compl {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) (hsup : σ.support = univ) :
    (σ * c⁻¹).support = c.supportᶜ := by
  ext x
  constructor
  · intro hxrem
    by_cases hx : x ∈ c.support
    · have : x ∉ (σ * c⁻¹).support :=
        Equiv.Perm.notMem_support.mpr (remainder_apply_eq_self_of_mem hc hx)
      exact (this hxrem).elim
    · exact mem_compl.mpr hx
  · intro hxcompl
    have hx : x ∉ c.support := mem_compl.mp hxcompl
    have hcx : c x = x := Equiv.Perm.notMem_support.mp hx
    have hinv : c⁻¹ x = x := inv_apply_eq_self_of_apply_eq_self hcx
    refine Equiv.Perm.mem_support.mpr ?_
    change σ (c⁻¹ x) ≠ x
    rw [hinv]
    exact Equiv.Perm.mem_support.mp (hsup.symm ▸ mem_univ x)

lemma ofSubtype_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    Equiv.Perm.ofSubtype
        (c.subtypePerm fun x =>
          (mem_of_support_subset (s := c.support) (Subset.rfl) x).symm) *
      (σ * c⁻¹) = σ := by
  rw [ofSubtype_subtypePerm_of_support_subset (s := c.support) Subset.rfl]
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  rw [← hd.commute.eq]
  simp

lemma not_mem_support_of_mem_of_subset_compl {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} {τ : Perm α} (hτ : τ.support ⊆ sᶜ) {x : α} (hx : x ∈ s) :
    τ x = x :=
  Equiv.Perm.notMem_support.mp fun h => (mem_compl.mp (hτ h)) hx

lemma cycleOf_mul_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ) {x : α} (hx : x ∈ s) :
    (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).cycleOf x =
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) := by
  have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ
  have hτx : τ x = x := not_mem_support_of_mem_of_subset_compl hτ hx
  have hcycle := ofSubtype_isCycle (listingPerm_isCycle (p := p) e hcard)
  have hne : Equiv.Perm.ofSubtype (listingPerm (p := p) e) x ≠ x :=
    Equiv.Perm.mem_support.mp (by
      rw [support_ofSubtype_listing p e hcard]
      exact hx)
  rw [Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hd.commute x hτx]
  exact Equiv.Perm.IsCycle.cycleOf_eq hcycle hne

lemma longPoints_mul_listing {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (p : {a // a ∈ s})
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (hs : 3 ≤ s.card) {τ : Perm α} (hτ : τ.support ⊆ sᶜ) :
    longPoints (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) =
      s ∪ longPoints τ := by
  ext x
  by_cases hx : x ∈ s
  · have hcy := cycleOf_mul_listing p e hcard hτ hx
    have hsup : (Equiv.Perm.ofSubtype (listingPerm (p := p) e)).support = s :=
      support_ofSubtype_listing p e hcard
    simp only [mem_longPoints, mem_union, hx, true_or, iff_true]
    rw [hcy, hsup]
    exact hs
  · have hd := ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ
    have hfx : Equiv.Perm.ofSubtype (listingPerm (p := p) e) x = x :=
      Equiv.Perm.notMem_support.mp (by
        rw [support_ofSubtype_listing p e hcard]
        exact hx)
    have hcy : (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ).cycleOf x =
        τ.cycleOf x := by
      rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hd,
        (Equiv.Perm.cycleOf_eq_one_iff _).mpr hfx, one_mul]
    simp only [mem_longPoints, mem_union, hx, false_or]
    rw [hcy]

noncomputable def longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) : Finset α × Perm α :=
  if h : (longPoints σ).Nonempty then
    ((σ.cycleOf ((longPoints σ).min' h)).support,
      σ * (σ.cycleOf ((longPoints σ).min' h))⁻¹)
  else
    (∅, 1)

lemma sum_eq_sum_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (g : Perm α → ℂ) :
    ∑ σ : Perm α, g σ =
      ∑ s : Finset α, ∑ τ : Perm α,
        ∑ σ : Perm α, if longKey σ = (s, τ) then g σ else 0 := by
  have hσ : ∀ σ : Perm α,
      g σ = ∑ s : Finset α, ∑ τ : Perm α,
        if longKey σ = (s, τ) then g σ else 0 := by
    intro σ
    have hpair :
        (∑ p : Finset α × Perm α, if longKey σ = p then g σ else 0) = g σ := by
      rw [sum_ite_eq, if_pos (mem_univ _)]
    have hprod :
        (∑ p : Finset α × Perm α, if longKey σ = p then g σ else 0) =
          ∑ s : Finset α, ∑ τ : Perm α,
            if longKey σ = (s, τ) then g σ else 0 := by
      exact Fintype.sum_prod_type
        (fun p : Finset α × Perm α => if longKey σ = p then g σ else 0)
    exact hpair.symm.trans hprod
  refine (Fintype.sum_congr _ _ hσ).trans ?_
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun s => ?_
  rw [sum_comm]

lemma min'_union_eq_of_le {α : Type*} [DecidableEq α] [LinearOrder α] {s t : Finset α}
    (hs : s.Nonempty) (h : ∀ a ∈ t, s.min' hs ≤ a) :
    (s ∪ t).min' (hs.mono subset_union_left) = s.min' hs := by
  apply le_antisymm
  · exact (isLeast_min' (s ∪ t) (hs.mono subset_union_left)).2
      (mem_union.mpr (Or.inl (min'_mem s hs)))
  · have hmem := min'_mem (s ∪ t) (hs.mono subset_union_left)
    rcases mem_union.mp hmem with hys | hyt
    · exact (isLeast_min' s hs).2 hys
    · exact h _ hyt

lemma mul_right_inv_eq_of_disjoint {α : Type*} {f τ : Perm α}
    (h : Equiv.Perm.Disjoint f τ) : (f * τ) * f⁻¹ = τ := by
  rw [h.commute.eq]
  simp

lemma longKey_of_listing {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {s : Finset α} (hsn : s.Nonempty) (hs : 3 ≤ s.card)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support ⊆ sᶜ)
    (hdist : ∀ a ∈ longPoints τ, p.1 ≤ a) :
    longKey (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = (s, τ) := by
  set f := Equiv.Perm.ofSubtype (listingPerm (p := p) e)
  set σ := f * τ
  have hlp : longPoints σ = s ∪ longPoints τ :=
    longPoints_mul_listing p e hcard hs hτ
  have hne : (longPoints σ).Nonempty := by
    rw [hlp]
    exact ⟨p.1, mem_union.mpr (Or.inl p.2)⟩
  have hmin : (longPoints σ).min' hne = p.1 := by
    have hmin' :
        (s ∪ longPoints τ).min' (hsn.mono subset_union_left) = s.min' hsn :=
      min'_union_eq_of_le hsn (fun a ha => hp ▸ hdist a ha)
    refine Eq.trans ?_ (hp ▸ hmin')
    congr 1
  have hcy : σ.cycleOf ((longPoints σ).min' hne) = f := by
    rw [hmin]
    have hx : p.1 ∈ s := p.2
    exact cycleOf_mul_listing p e hcard hτ hx
  unfold longKey
  rw [dif_pos hne]
  apply Prod.ext
  · change (σ.cycleOf ((longPoints σ).min' hne)).support = s
    rw [hcy]
    exact support_ofSubtype_listing p e hcard
  · change σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ = τ
    rw [hcy]
    exact mul_right_inv_eq_of_disjoint
      (ofSubtype_disjoint_of_support_subset_compl (listingPerm (p := p) e) hτ)

lemma isCycle_subtypePerm_of_support {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} (hc : c.IsCycle) (h2 : 2 ≤ c.support.card) :
    (c.subtypePerm fun x =>
      (mem_of_support_subset (s := c.support) Subset.rfl x).symm).IsCycle := by
  have hon : c.IsCycleOn (c.support : Set α) := by
    convert hc.isCycleOn
    ext x
    simp [Equiv.Perm.mem_support]
  have hnt : (c.support : Set α).Nontrivial := by
    obtain ⟨a, b, ha, hb, hne⟩ := (one_lt_card_iff (s := c.support)).1 (by omega)
    exact ⟨a, ha, b, hb, hne⟩
  convert hon.isCycle_subtypePerm hnt

lemma support_subtypePerm_univ {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} :
    (c.subtypePerm fun x =>
      (mem_of_support_subset (s := c.support) Subset.rfl x).symm).support = univ := by
  ext q
  constructor
  · intro _hq
    exact mem_univ q
  · intro _hq
    rw [Equiv.Perm.support_subtypePerm]
    exact mem_filter.mpr ⟨mem_univ q, Equiv.Perm.mem_support.mp q.2⟩

lemma support_cycleOf_subset_longPoints {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {a : α} (h : 3 ≤ (σ.cycleOf a).support.card) :
    (σ.cycleOf a).support ⊆ longPoints σ := by
  intro x hx
  have hsc : σ.SameCycle a x := (Equiv.Perm.mem_support_cycleOf_iff.mp hx).1
  rw [mem_longPoints, ← hsc.cycleOf_eq]
  exact h

lemma eq_listing_of_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (_hsupσ : σ.support = univ) :
    ∃ (hsn : s.Nonempty) (_hs : 3 ≤ s.card)
      (p : {a // a ∈ s}) (_hp : p.1 = s.min' hsn)
      (_hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
      (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p}),
        Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ = σ := by
  let pα := (longPoints σ).min' hne
  let c := σ.cycleOf pα
  have hlong : longKey σ = (c.support, σ * c⁻¹) := by
    dsimp [longKey]
    rw [dif_pos hne]
  rw [hlong] at hkey
  rw [show s = c.support from (congrArg Prod.fst hkey).symm]
  rw [show τ = σ * c⁻¹ from (congrArg Prod.snd hkey).symm]
  have hpα : pα ∈ longPoints σ := min'_mem _ hne
  have h3 : 3 ≤ c.support.card := mem_longPoints.mp hpα
  have hpαs : pα ∈ c.support := by
    have hneσ : σ pα ≠ pα := by
      intro h
      have h1 : c = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
      have h0 : c.support.card = 0 := by
        rw [h1, Equiv.Perm.support_one, card_empty]
      omega
    have : c pα ≠ pα := by
      rwa [Equiv.Perm.cycleOf_apply_self]
    exact Equiv.Perm.mem_support.mpr this
  have hpσ' : pα ∈ σ.support := by
    have : c pα ≠ pα := Equiv.Perm.mem_support.mp hpαs
    rwa [Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_apply_self]
  have hcmem : c ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 hpσ'
  have hsn : c.support.Nonempty := ⟨pα, hpαs⟩
  refine ⟨hsn, h3, ⟨pα, hpαs⟩, ?_, two_le_card_subtype_ne_of_card_three ⟨pα, hpαs⟩ h3, ?_, ?_⟩
  · apply le_antisymm
    · exact (isLeast_min' (longPoints σ) hne).2
        (support_cycleOf_subset_longPoints h3 (min'_mem c.support hsn))
    · exact (isLeast_min' c.support hsn).2 hpαs
  · have hcyc : c.IsCycle :=
      Equiv.Perm.isCycle_cycleOf _ (Equiv.Perm.mem_support.mp hpσ')
    exact ncycleToListing (isCycle_subtypePerm_of_support hcyc (by omega))
      (support_subtypePerm_univ (c := c))
  · have hcyc : c.IsCycle :=
      Equiv.Perm.isCycle_cycleOf _ (Equiv.Perm.mem_support.mp hpσ')
    have hu := isCycle_subtypePerm_of_support hcyc (by omega)
    have hsupu := support_subtypePerm_univ (c := c)
    have heq :
        listingPerm (p := ⟨pα, hpαs⟩) (ncycleToListing hu hsupu) =
          c.subtypePerm fun x =>
            (mem_of_support_subset (s := c.support) Subset.rfl x).symm :=
      listingPerm_ncycleToListing hu hsupu
    rw [heq]
    exact ofSubtype_mul_remainder hcmem

lemma cycleOf_min_ne_self {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    σ ((longPoints σ).min' hne) ≠ (longPoints σ).min' hne := by
  intro h
  have h1 : σ.cycleOf ((longPoints σ).min' hne) = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff σ).mpr h
  have h3 : 3 ≤ (σ.cycleOf ((longPoints σ).min' hne)).support.card :=
    mem_longPoints.mp (min'_mem _ hne)
  have h0 : (σ.cycleOf ((longPoints σ).min' hne)).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  omega

lemma cycleOf_min_mem_cycleFactorsFinset {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    σ.cycleOf ((longPoints σ).min' hne) ∈ σ.cycleFactorsFinset :=
  (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
    (Equiv.Perm.mem_support.mpr (cycleOf_min_ne_self hne))

lemma longKey_eq {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (longPoints σ).Nonempty) :
    longKey σ =
      ((σ.cycleOf ((longPoints σ).min' hne)).support,
        σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹) := by
  dsimp [longKey]
  rw [dif_pos hne]

lemma three_le_card_fst_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty) :
    3 ≤ s.card := by
  rw [show s = (σ.cycleOf ((longPoints σ).min' hne)).support from
    congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))]
  exact mem_longPoints.mp (min'_mem _ hne)

lemma remainder_support_of_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (hsup : σ.support = univ) : τ.support = sᶜ := by
  rw [show τ = σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ from
      congrArg Prod.snd (hkey.symm.trans (longKey_eq hne)),
    show s = (σ.cycleOf ((longPoints σ).min' hne)).support from
      congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))]
  exact remainder_support_eq_compl (cycleOf_min_mem_cycleFactorsFinset hne) hsup

lemma eq_mul_remainder_of_mem_cycleFactorsFinset {α : Type*} [Fintype α]
    [DecidableEq α] {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    σ = c * (σ * c⁻¹) := by
  have h := ofSubtype_mul_remainder hc
  rw [ofSubtype_subtypePerm_of_support_subset (s := c.support) Subset.rfl] at h
  exact h.symm

lemma longPoints_mul_inv_cycle_subset {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    longPoints (σ * c⁻¹) ⊆ longPoints σ := by
  intro a ha
  rw [mem_longPoints] at ha ⊢
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  by_cases hx : a ∈ c.support
  · have hfix : (σ * c⁻¹) a = a := remainder_apply_eq_self_of_mem hc hx
    have h1 : (σ * c⁻¹).cycleOf a = 1 :=
      (Equiv.Perm.cycleOf_eq_one_iff (σ * c⁻¹)).mpr hfix
    have h0 : ((σ * c⁻¹).cycleOf a).support.card = 0 := by
      rw [h1, Equiv.Perm.support_one, card_empty]
    omega
  · have hcx : c a = a := Equiv.Perm.notMem_support.mp hx
    have hc1 : c.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff c).mpr hcx
    have hcy : σ.cycleOf a = (σ * c⁻¹).cycleOf a := by
      have hleft : σ.cycleOf a = (c * (σ * c⁻¹)).cycleOf a :=
        congrArg (fun f => f.cycleOf a) hσeq
      rw [hleft, Equiv.Perm.Disjoint.cycleOf_mul_distrib hd.symm a, hc1, one_mul]
    rwa [hcy]

lemma min'_fst_eq_min'_longPoints {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hsn : s.Nonempty) (hkey : longKey σ = (s, τ))
    (hne : (longPoints σ).Nonempty) :
    s.min' hsn = (longPoints σ).min' hne := by
  have hs : s = (σ.cycleOf ((longPoints σ).min' hne)).support :=
    congrArg Prod.fst (hkey.symm.trans (longKey_eq hne))
  apply le_antisymm
  · have hpαs : (longPoints σ).min' hne ∈ s := by
      rw [hs]
      exact Equiv.Perm.mem_support.mpr (by
        rw [Equiv.Perm.cycleOf_apply_self]
        exact cycleOf_min_ne_self hne)
    exact (isLeast_min' s hsn).2 hpαs
  · have hsub : s ⊆ longPoints σ := by
      rw [hs]
      exact support_cycleOf_subset_longPoints (mem_longPoints.mp (min'_mem _ hne))
    exact (isLeast_min' (longPoints σ) hne).2 (hsub (min'_mem s hsn))

lemma dist_of_longKey {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} {s : Finset α} {τ : Perm α} (hsn : s.Nonempty)
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty) :
    ∀ a ∈ longPoints τ, s.min' hsn ≤ a := by
  have hτ : τ = σ * (σ.cycleOf ((longPoints σ).min' hne))⁻¹ :=
    congrArg Prod.snd (hkey.symm.trans (longKey_eq hne))
  intro a ha
  have hsub : longPoints τ ⊆ longPoints σ := by
    rw [hτ]
    exact longPoints_mul_inv_cycle_subset (cycleOf_min_mem_cycleFactorsFinset hne)
  have hle : (longPoints σ).min' hne ≤ a :=
    (isLeast_min' (longPoints σ) hne).2 (hsub ha)
  rw [min'_fst_eq_min'_longPoints hsn hkey hne]
  exact hle

lemma listingPerm_injective {α : Type*} [Fintype α] [DecidableEq α] {p : α}
    (hcard : 2 ≤ Fintype.card {q : α // q ≠ p}) :
    Function.Injective (listingPerm (p := p)) := by
  intro e₁ e₂ h
  exact (listingEquiv p hcard).injective (Subtype.ext h)

lemma ofSubtype_listing_mul_injective {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (p : {a // a ∈ s})
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    (τ : Perm α) :
    Function.Injective fun e =>
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ := by
  intro e₁ e₂ h
  have h' : Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) * τ =
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) * τ := h
  have hf :
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) =
        Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) := by
    calc
      Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) =
          Equiv.Perm.ofSubtype (listingPerm (p := p) e₁) * τ * τ⁻¹ := by simp
      _ = Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) * τ * τ⁻¹ := by rw [h']
      _ = Equiv.Perm.ofSubtype (listingPerm (p := p) e₂) := by simp
  exact listingPerm_injective hcard (Equiv.Perm.ofSubtype_injective hf)

lemma listing_mem_long_fiber {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {s : Finset α} (hsn : s.Nonempty) (hs : 3 ≤ s.card)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    (hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p})
    {τ : Perm α} (hτ : τ.support = sᶜ)
    (hdist : ∀ a ∈ longPoints τ, p.1 ≤ a)
    (e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃ {q : {a // a ∈ s} // q ≠ p}) :
    longKey (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) = (s, τ) ∧
      (∀ i, (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ) i ≠ i) ∧
        (longPoints (Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ)).Nonempty := by
  have hsub : τ.support ⊆ sᶜ := hτ ▸ Subset.rfl
  refine ⟨longKey_of_listing hsn hs p hp e hcard hsub hdist, ?_, ?_⟩
  · intro i
    have hsup := support_mul_listing_τ p e hcard hτ
    exact Equiv.Perm.mem_support.mp (by
      rw [hsup]
      exact mem_univ i)
  · rw [longPoints_mul_listing p e hcard hs hsub]
    exact hsn.mono subset_union_left

lemma mem_range_listing_of_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {s : Finset α} (hsn : s.Nonempty)
    (p : {a // a ∈ s}) (hp : p.1 = s.min' hsn)
    {τ σ : Perm α} (hkey : longKey σ = (s, τ))
    (hne : (longPoints σ).Nonempty) (hsup : σ.support = univ) :
    ∃ e : Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃
        {q : {a // a ∈ s} // q ≠ p},
      Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ = σ := by
  obtain ⟨hsn', _hs, p', hp', _hcard, e, heq⟩ := eq_listing_of_longKey hkey hne hsup
  have hp_eq : p' = p := Subtype.ext <|
    hp'.trans <|
      (le_antisymm
          ((isLeast_min' s hsn').2 (min'_mem s hsn))
          ((isLeast_min' s hsn).2 (min'_mem s hsn'))).trans
        hp.symm
  subst hp_eq
  exact ⟨e, heq⟩

lemma long_fiber_inv_one_sub {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  by_cases hs3 : 3 ≤ s.card
  · have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
    by_cases hτ : τ.support = sᶜ
    · by_cases hdist : ∀ a ∈ longPoints τ, s.min' hsn ≤ a
      · let p : {a // a ∈ s} := ⟨s.min' hsn, min'_mem s hsn⟩
        have hp : p.1 = s.min' hsn := rfl
        have hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} :=
          two_le_card_subtype_ne_of_card_three (p := p) hs3
        let φ : (Fin (Fintype.card {q : {a // a ∈ s} // q ≠ p}) ≃
            {q : {a // a ∈ s} // q ≠ p}) → Perm (Fin N) := fun e =>
          Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ
        have hinj : Function.Injective φ :=
          ofSubtype_listing_mul_injective (p := p) hcard τ
        have hsum := inv_one_sub_replace_cycle (p := p) hζ hcard hτ
        refine Eq.trans ?_ hsum
        refine (Fintype.sum_of_injective φ hinj
            (fun e => ∏ i : Fin N,
              (1 - ζ ^ ((φ e i).val - i.val : ℤ))⁻¹)
            (fun σ =>
              if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
                ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
              else 0)
            ?_ ?_).symm
        · intro σ hσ
          split_ifs with hfiber
          · exact (hσ (Set.mem_range.mpr (mem_range_listing_of_longKey hsn p hp
              hfiber.1 hfiber.2.2 (derangement_support_univ hfiber.2.1)))).elim
          · rfl
        · intro e
          have hdist' : ∀ a ∈ longPoints τ, p.1 ≤ a := by
            intro a ha
            rw [hp]
            exact hdist a ha
          have hmem := listing_mem_long_fiber hsn hs3 p hp hcard hτ hdist' e
          have hφ : φ e = Equiv.Perm.ofSubtype (listingPerm (p := p) e) * τ := rfl
          rw [hφ, if_pos hmem]
      · have h0 : ∀ σ : Perm (Fin N),
            (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
              ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
            else 0) = 0 := by
          intro σ
          split_ifs with hfiber
          · exact (hdist (dist_of_longKey hsn hfiber.1 hfiber.2.2)).elim
          · rfl
        exact (Fintype.sum_congr _ _ h0).trans (by simp)
    · have h0 : ∀ σ : Perm (Fin N),
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) = 0 := by
        intro σ
        split_ifs with hfiber
        · exact (hτ (remainder_support_of_longKey hfiber.1 hfiber.2.2
            (derangement_support_univ hfiber.2.1))).elim
        · rfl
      exact (Fintype.sum_congr _ _ h0).trans (by simp)
  · have h0 : ∀ σ : Perm (Fin N),
        (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) = 0 := by
      intro σ
      split_ifs with hfiber
      · exact (hs3 (three_le_card_fst_longKey hfiber.1 hfiber.2.2)).elim
      · rfl
    exact (Fintype.sum_congr _ _ h0).trans (by simp)

lemma ite_longKey_and {N : ℕ} {s : Finset (Fin N)} {τ : Perm (Fin N)}
    (g : Perm (Fin N) → ℂ) (σ : Perm (Fin N)) :
    (if longKey σ = (s, τ) then
        if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then g σ else 0
      else 0) =
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        g σ
      else 0 := by
  by_cases hkey : longKey σ = (s, τ)
  · by_cases hdl : (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty
    · simp [hkey, hdl]
    · simp [hkey, hdl]
  · simp [hkey]

lemma long_cycle_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) :
    (∑ σ : Perm (Fin N),
      if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  rw [sum_eq_sum_longKey (fun σ =>
    if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
      ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
    else 0)]
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ =>
        Fintype.sum_congr _ _ fun σ =>
          ite_longKey_and (fun σ =>
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹) σ) ?_
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ => long_fiber_inv_one_sub hζ s τ) (by simp)

lemma coe_sign_mul {α : Type*} [Fintype α] [DecidableEq α] (f g : Perm α) :
    (Perm.sign (f * g) : ℂ) = (Perm.sign f : ℂ) * (Perm.sign g : ℂ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]

lemma coe_sign_isCycle {α : Type*} [Fintype α] [DecidableEq α] {f : Perm α}
    (hf : f.IsCycle) :
    (Perm.sign f : ℂ) = -(-1 : ℂ) ^ f.support.card := by
  rw [Equiv.Perm.IsCycle.sign hf]
  rw [Units.val_neg, Int.cast_neg, coe_units_neg_one_pow]

lemma sign_eq_of_mem_longKey {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} {s : Finset α} {τ : Perm α}
    (hkey : longKey σ = (s, τ)) (hne : (longPoints σ).Nonempty)
    (hsup : σ.support = univ) :
    (Perm.sign σ : ℂ) = -(-1 : ℂ) ^ s.card * (Perm.sign τ : ℂ) := by
  have hs3 := three_le_card_fst_longKey hkey hne
  have hsn : s.Nonempty := Finset.card_pos.mp (by omega)
  let p : {a // a ∈ s} := ⟨s.min' hsn, min'_mem s hsn⟩
  have hp : p.1 = s.min' hsn := rfl
  have hcard : 2 ≤ Fintype.card {q : {a // a ∈ s} // q ≠ p} :=
    two_le_card_subtype_ne_of_card_three (p := p) hs3
  obtain ⟨e, heq⟩ := mem_range_listing_of_longKey hsn p hp hkey hne hsup
  have hcyc := ofSubtype_isCycle (listingPerm_isCycle (p := p) e hcard)
  rw [← heq, coe_sign_mul, coe_sign_isCycle hcyc, support_ofSubtype_listing p e hcard]

lemma long_fiber_signed_inv_one_sub {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (s : Finset (Fin N)) (τ : Perm (Fin N)) :
    (∑ σ : Perm (Fin N),
      if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  have hterm : ∀ σ : Perm (Fin N),
      (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (-(-1 : ℂ) ^ s.card * (Perm.sign τ : ℂ)) *
          (if longKey σ = (s, τ) ∧ (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
            ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    split_ifs with h
    · rw [sign_eq_of_mem_longKey h.1 h.2.2 (derangement_support_univ h.2.1)]
    · rw [mul_zero]
  simp_rw [hterm, ← mul_sum, long_fiber_inv_one_sub hζ s τ, mul_zero]

lemma long_cycle_signed_inv_one_sub_sum {N : ℕ} [NeZero N] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) :
    (∑ σ : Perm (Fin N),
      if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
        (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) = 0 := by
  rw [sum_eq_sum_longKey (fun σ =>
    if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
      (Perm.sign σ : ℂ) * ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
    else 0)]
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ =>
        Fintype.sum_congr _ _ fun σ =>
          ite_longKey_and (fun σ =>
            (Perm.sign σ : ℂ) *
              ∏ i : Fin N, (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹) σ) ?_
  refine Eq.trans (Fintype.sum_congr _ _ fun s =>
      Fintype.sum_congr _ _ fun τ => long_fiber_signed_inv_one_sub hζ s τ) (by simp)

lemma not_mem_longPoints_of_cycleType_eq_two {n : ℕ} {σ : Perm (Fin (2 * n))}
    (h : σ.cycleType = Multiset.replicate n 2) {a : Fin (2 * n)} :
    a ∉ longPoints σ := by
  intro ha
  rw [mem_longPoints] at ha
  have hne : σ a ≠ a := by
    intro hfix
    have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
    have h0 : (σ.cycleOf a).support.card = 0 := by
      rw [h1, Equiv.Perm.support_one, card_empty]
    omega
  have hcmem : σ.cycleOf a ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 (Equiv.Perm.mem_support.mpr hne)
  have hmem : (σ.cycleOf a).support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr ⟨σ.cycleOf a, Finset.mem_def.mp hcmem, rfl⟩
  have heq2 : (σ.cycleOf a).support.card = 2 :=
    (Multiset.mem_replicate.mp (h ▸ hmem)).2
  omega

lemma derangement_inv_one_sub_eq_involution {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      ∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) +
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    by_cases hder : ∀ i, σ i ≠ i
    · have hcases :=
        derangement_long_cycle_or_replicate_two (derangement_support_univ hder)
      rcases hcases with hL | hinv
      · have hne : (longPoints σ).Nonempty := longPoints_nonempty_iff.2 hL
        have hninv : ¬ σ.cycleType = Multiset.replicate n 2 := by
          intro hct
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hct ha
        rw [if_pos hder, if_pos ⟨hder, hne⟩,
          if_neg (mt And.right hninv), add_zero]
      · have hnlong : ¬ (longPoints σ).Nonempty := by
          intro hne
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hinv ha
        rw [if_pos hder, if_neg (mt And.right hnlong), if_pos ⟨hder, hinv⟩,
          zero_add]
    · rw [if_neg hder, if_neg (mt And.left hder), if_neg (mt And.left hder),
        add_zero]
  refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
  rw [sum_add_distrib, long_cycle_inv_one_sub_sum (N := 2 * n) ‹_›, zero_add]

lemma signed_derangement_eq_involution {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (_hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      ∑ σ : Perm (Fin (2 * n)),
        if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
          (Perm.sign σ : ℂ) *
            ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hterm : ∀ σ : Perm (Fin (2 * n)),
      (if (∀ i, σ i ≠ i) then
        (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
        (if (∀ i, σ i ≠ i) ∧ (longPoints σ).Nonempty then
          (Perm.sign σ : ℂ) * ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
        else 0) +
          (if (∀ i, σ i ≠ i) ∧ σ.cycleType = Multiset.replicate n 2 then
            (Perm.sign σ : ℂ) *
              ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
          else 0) := by
    intro σ
    by_cases hder : ∀ i, σ i ≠ i
    · have hcases :=
        derangement_long_cycle_or_replicate_two (derangement_support_univ hder)
      rcases hcases with hL | hinv
      · have hne : (longPoints σ).Nonempty := longPoints_nonempty_iff.2 hL
        have hninv : ¬ σ.cycleType = Multiset.replicate n 2 := by
          intro hct
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hct ha
        rw [if_pos hder, if_pos ⟨hder, hne⟩,
          if_neg (mt And.right hninv), add_zero]
      · have hnlong : ¬ (longPoints σ).Nonempty := by
          intro hne
          obtain ⟨a, ha⟩ := hne
          exact not_mem_longPoints_of_cycleType_eq_two hinv ha
        rw [if_pos hder, if_neg (mt And.right hnlong), if_pos ⟨hder, hinv⟩,
          zero_add]
    · rw [if_neg hder, if_neg (mt And.left hder), if_neg (mt And.left hder),
        add_zero]
  refine Eq.trans (Fintype.sum_congr _ _ hterm) ?_
  rw [sum_add_distrib, long_cycle_signed_inv_one_sub_sum (N := 2 * n) ‹_›, zero_add]

lemma unsigned_derangement_inv_sum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (∑ σ : Perm (Fin (2 * n)),
      if (∀ i, σ i ≠ i) then
        ∏ i : Fin (2 * n), (1 - ζ ^ ((σ i).val - i.val : ℤ))⁻¹
      else 0) =
      (a n : ℂ) / (2 : ℂ) ^ (2 * n) := by
  rw [derangement_inv_one_sub_eq_involution hn hζ, involution_unsigned_eq_neg_signed,
    ← signed_derangement_eq_involution hn hζ, signed_derangement_inv_sum hn hζ,
    ← mul_div_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
    one_mul]

lemma permanent_sunMatrix_sub_ones_eq_a {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ - allOnes (2 * n)).permanent = (a n : ℂ) := by
  have h2 : (2 : ℂ) ^ (2 * n) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [permanent_sunMatrix_sub_ones hn hζ, unsigned_derangement_inv_sum hn hζ]
  exact mul_div_cancel₀ _ h2

/-- Cayley-kernel weight of a permutation. The empty product is 1. -/
noncomputable def cayleyWeight {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) : ℂ :=
  ∏ i ∈ σ.support, (x i + x (σ i)) / (x i - x (σ i))

lemma cayleyFactor_swap {R : Type*} [Field R] (a b : R) :
    (b + a) / (b - a) = -((a + b) / (a - b)) := by
  by_cases h : a = b
  · simp [h]
  · have hab : a - b ≠ 0 := sub_ne_zero.2 h
    have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    field_simp [hab, hba]
    ring

lemma cayleyWeight_one {α : Type*} [Fintype α] [DecidableEq α] (x : α → ℂ) :
    cayleyWeight x (1 : Perm α) = 1 := by
  simp [cayleyWeight]

lemma cayleyWeight_mul_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ τ : Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    cayleyWeight x (σ * τ) = cayleyWeight x σ * cayleyWeight x τ := by
  simp only [cayleyWeight]
  rw [h.support_mul, prod_union h.disjoint_support]
  refine congr_arg₂ (· * ·) ?_ ?_
  · refine prod_congr rfl fun a ha => ?_
    have hτ : τ a = a := Equiv.Perm.notMem_support.mp (h.mem_imp ha)
    simp [hτ]
  · refine prod_congr rfl fun a ha => ?_
    have hσa : σ (τ a) = τ a := by
      have : τ a ∈ τ.support := (Equiv.Perm.apply_mem_support (f := τ)).2 ha
      exact Equiv.Perm.notMem_support.mp (h.symm.mem_imp this)
    simp [hσa]

lemma cayleyWeight_inv {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) (σ : Perm α) :
    cayleyWeight x σ⁻¹ = (-1 : ℂ) ^ σ.support.card * cayleyWeight x σ := by
  have hsup : σ⁻¹.support = σ.support := Equiv.Perm.support_inv σ
  unfold cayleyWeight
  rw [hsup]
  have hterm : ∀ i ∈ σ.support,
      (x i + x (σ⁻¹ i)) / (x i - x (σ⁻¹ i)) =
        -((x (σ⁻¹ i) + x i) / (x (σ⁻¹ i) - x i)) := fun i _ =>
    cayleyFactor_swap (x (σ⁻¹ i)) (x i)
  rw [prod_congr rfl hterm, prod_neg]
  refine congr_arg ((-1 : ℂ) ^ σ.support.card * ·) ?_
  refine prod_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i ∈ σ⁻¹.support := by rwa [hsup]
    have : σ⁻¹ i ∈ σ⁻¹.support := Equiv.Perm.apply_mem_support.mpr hi'
    rwa [hsup] at this
  · intro i _ i' _ h
    exact σ⁻¹.injective h
  · intro j hj
    refine ⟨σ j, Equiv.Perm.apply_mem_support.mpr hj, ?_⟩
    simp
  · intro i _hi
    simp

lemma cayley_add_eq {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ i.val + ζ ^ j.val =
      ζ ^ i.val * (1 + ζ ^ (j.val - i.val : ℤ)) := by
  have hz := zeta_ne_zero hζ
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ hz
  have hdiv : ζ ^ j.val / ζ ^ i.val = ζ ^ (j.val - i.val : ℤ) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
  have hsplit : ζ ^ i.val + ζ ^ j.val =
      ζ ^ i.val * (1 + ζ ^ j.val / ζ ^ i.val) := by
    field_simp [hi]
  rw [hsplit, hdiv]

lemma cayley_sub_eq {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (i j : Fin N) :
    ζ ^ i.val - ζ ^ j.val =
      ζ ^ i.val * (1 - ζ ^ (j.val - i.val : ℤ)) := by
  rw [← neg_sub, zeta_pow_sub hζ i j, neg_mul, neg_neg]

lemma cayley_eq_sunFactor {N : ℕ} [NeZero N] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {i j : Fin N} (hij : i ≠ j) :
    (ζ ^ i.val + ζ ^ j.val) / (ζ ^ i.val - ζ ^ j.val) =
      (1 + ζ ^ (j.val - i.val : ℤ)) / (1 - ζ ^ (j.val - i.val : ℤ)) := by
  have hi : ζ ^ i.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero hζ)
  have hden := denom_ne_zero hζ hij.symm
  rw [cayley_add_eq hζ i j, cayley_sub_eq hζ i j]
  field_simp [hi, hden]

lemma prod_sunMatrix_eq_cayleyWeight {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) (σ : Perm (Fin (2 * n))) :
    (∏ i : Fin (2 * n), sunMatrix n ζ (σ i) i) =
      cayleyWeight (fun i => ζ ^ i.val) σ := by
  unfold cayleyWeight
  rw [← union_compl σ.support, prod_union disjoint_compl_right]
  have hfix : ∏ i ∈ σ.supportᶜ, sunMatrix n ζ (σ i) i = 1 := by
    refine prod_eq_one fun i hi => ?_
    have : σ i = i := Equiv.Perm.notMem_support.mp (mem_compl.mp hi)
    rw [this, sunMatrix_apply_eq]
  rw [hfix, mul_one]
  refine prod_congr rfl fun i hi => ?_
  have hne : σ i ≠ i := Equiv.Perm.mem_support.mp hi
  rw [sunMatrix_apply_ne hζ hne]
  exact (cayley_eq_sunFactor (N := 2 * n) hζ hne.symm).symm

lemma permanent_sunMatrix_eq_sum_cayleyWeight {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent =
      ∑ σ : Perm (Fin (2 * n)), cayleyWeight (fun i => ζ ^ i.val) σ := by
  have : NeZero n := ⟨by omega⟩
  unfold Matrix.permanent
  refine Fintype.sum_congr _ _ fun σ =>
    prod_sunMatrix_eq_cayleyWeight hζ σ

/-- Points that lie on an odd-length cycle. Cycle factors have length at least 2,
so these cycles have length at least 3. -/
noncomputable def oddLongPoints {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    Finset α :=
  univ.filter fun a => Odd ((σ.cycleOf a).support.card)

lemma mem_oddLongPoints {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} {a : α} :
    a ∈ oddLongPoints σ ↔ Odd ((σ.cycleOf a).support.card) := by
  simp [oddLongPoints]

lemma odd_card_cycleOf_ne_self {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {a : α} (h : Odd ((σ.cycleOf a).support.card)) : σ a ≠ a := by
  intro hfix
  have h1 : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
  have h0 : (σ.cycleOf a).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  exact Nat.not_odd_zero (h0 ▸ h)

lemma oddLongPoints_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    (oddLongPoints σ).Nonempty ↔ ∃ c ∈ σ.cycleFactorsFinset, Odd c.support.card := by
  constructor
  · intro ⟨a, ha⟩
    rw [mem_oddLongPoints] at ha
    exact ⟨σ.cycleOf a, (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
      (Equiv.Perm.mem_support.mpr (odd_card_cycleOf_ne_self ha)), ha⟩
  · intro ⟨c, hc, hodd⟩
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    refine ⟨a, mem_oddLongPoints.mpr ?_⟩
    rwa [← Equiv.Perm.cycle_is_cycleOf ha hc]

lemma odd_cycleOf_min_ne_self {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    σ ((oddLongPoints σ).min' hne) ≠ (oddLongPoints σ).min' hne :=
  odd_card_cycleOf_ne_self (mem_oddLongPoints.mp (min'_mem _ hne))

lemma odd_cycleOf_min_mem_cycleFactorsFinset {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    σ.cycleOf ((oddLongPoints σ).min' hne) ∈ σ.cycleFactorsFinset :=
  (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2
    (Equiv.Perm.mem_support.mpr (odd_cycleOf_min_ne_self hne))

lemma odd_cycleOf_min_odd {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (hne : (oddLongPoints σ).Nonempty) :
    Odd ((σ.cycleOf ((oddLongPoints σ).min' hne)).support.card) :=
  mem_oddLongPoints.mp (min'_mem _ hne)

lemma cayleyWeight_reverse_odd_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset)
    (hodd : Odd c.support.card) :
    cayleyWeight x (c⁻¹ * (σ * c⁻¹)) = - cayleyWeight x σ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  calc
    cayleyWeight x (c⁻¹ * (σ * c⁻¹))
        = cayleyWeight x c⁻¹ * cayleyWeight x (σ * c⁻¹) :=
      cayleyWeight_mul_disjoint x hdis
    _ = (-1 : ℂ) ^ c.support.card * cayleyWeight x c * cayleyWeight x (σ * c⁻¹) := by
      rw [cayleyWeight_inv]
    _ = - (cayleyWeight x c * cayleyWeight x (σ * c⁻¹)) := by
      rw [Odd.neg_one_pow hodd]
      ring
    _ = - cayleyWeight x (c * (σ * c⁻¹)) := by
      rw [cayleyWeight_mul_disjoint x hd.symm]
    _ = - cayleyWeight x σ := by
      rw [← hσeq]

lemma cycleOf_reverse_odd_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {a : α} (ha : a ∈ c.support) :
    (c⁻¹ * (σ * c⁻¹)).cycleOf a = c⁻¹ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hcyc : c⁻¹.IsCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.inv
  have hmem : c⁻¹ ∈ (c⁻¹ * (σ * c⁻¹)).cycleFactorsFinset := by
    rw [hdis.cycleFactorsFinset_mul_eq_union, hcyc.cycleFactorsFinset_eq_singleton]
    simp
  have ha' : a ∈ c⁻¹.support := by rwa [Equiv.Perm.support_inv]
  exact (Equiv.Perm.cycle_is_cycleOf ha' hmem).symm

lemma cycleOf_reverse_odd_of_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) {a : α} (ha : a ∉ c.support) :
    (c⁻¹ * (σ * c⁻¹)).cycleOf a = σ.cycleOf a := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hcx : c a = a := Equiv.Perm.notMem_support.mp ha
  have hc1 : c.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff c).mpr hcx
  have hinv1 : c⁻¹.cycleOf a = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff c⁻¹).mpr (inv_apply_eq_self_of_apply_eq_self hcx)
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hcyσ : σ.cycleOf a = (σ * c⁻¹).cycleOf a := by
    have hleft : σ.cycleOf a = (c * (σ * c⁻¹)).cycleOf a :=
      congrArg (fun f => f.cycleOf a) hσeq
    rw [hleft, Equiv.Perm.Disjoint.cycleOf_mul_distrib hd.symm a, hc1, one_mul]
  have hcyσ' : (c⁻¹ * (σ * c⁻¹)).cycleOf a = (σ * c⁻¹).cycleOf a := by
    rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hdis a, hinv1, one_mul]
  rw [hcyσ', hcyσ]

lemma oddLongPoints_reverse_odd_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    oddLongPoints (c⁻¹ * (σ * c⁻¹)) = oddLongPoints σ := by
  ext a
  simp only [mem_oddLongPoints]
  by_cases ha : a ∈ c.support
  · rw [cycleOf_reverse_odd_of_mem hc ha, Equiv.Perm.support_inv,
      Equiv.Perm.cycle_is_cycleOf ha hc]
  · rw [cycleOf_reverse_odd_of_not_mem hc ha]

/-- Reverse the distinguished odd cycle of `σ`, the cycle of the least odd-cycle point. -/
noncomputable def reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) : Perm α :=
  if h : (oddLongPoints σ).Nonempty then
    (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ *
      (σ * (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹)
  else
    σ

lemma reverseOddCycle_of_nonempty {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : (oddLongPoints σ).Nonempty) :
    reverseOddCycle σ =
      (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ *
        (σ * (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹) :=
  dif_pos h

lemma reverseOddCycle_of_empty {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : ¬ (oddLongPoints σ).Nonempty) :
    reverseOddCycle σ = σ :=
  dif_neg h

lemma cayleyWeight_reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) (σ : Perm α) :
    cayleyWeight x (reverseOddCycle σ) =
      if (oddLongPoints σ).Nonempty then - cayleyWeight x σ
      else cayleyWeight x σ := by
  by_cases h : (oddLongPoints σ).Nonempty
  · rw [if_pos h, reverseOddCycle_of_nonempty h]
    exact cayleyWeight_reverse_odd_cycle x
      (odd_cycleOf_min_mem_cycleFactorsFinset h) (odd_cycleOf_min_odd h)
  · rw [if_neg h, reverseOddCycle_of_empty h]

lemma oddLongPoints_reverseOddCycle {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (σ : Perm α) :
    oddLongPoints (reverseOddCycle σ) = oddLongPoints σ := by
  by_cases h : (oddLongPoints σ).Nonempty
  · rw [reverseOddCycle_of_nonempty h]
    exact oddLongPoints_reverse_odd_cycle (odd_cycleOf_min_mem_cycleFactorsFinset h)
  · rw [reverseOddCycle_of_empty h]

lemma reverseOddCycle_cycleOf_min {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {σ : Perm α} (h : (oddLongPoints σ).Nonempty) :
    (reverseOddCycle σ).cycleOf ((oddLongPoints σ).min' h) =
      (σ.cycleOf ((oddLongPoints σ).min' h))⁻¹ := by
  rw [reverseOddCycle_of_nonempty h]
  exact cycleOf_reverse_odd_of_mem (odd_cycleOf_min_mem_cycleFactorsFinset h)
    (Equiv.Perm.mem_support.mpr (by
      rw [Equiv.Perm.cycleOf_apply_self]
      exact odd_cycleOf_min_ne_self h))

lemma reverse_odd_cycle_mul_inv {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    c * ((c⁻¹ * (σ * c⁻¹)) * c) = σ := by
  have hd := Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc
  have hdis : Equiv.Perm.Disjoint c⁻¹ (σ * c⁻¹) := hd.symm.inv_left
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset hc
  have hmul : (c⁻¹ * (σ * c⁻¹)) * c = σ * c⁻¹ := by
    rw [hdis.commute.eq]
    simp
  rw [hmul, ← hσeq]

lemma reverseOddCycle_involutive {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] :
    Function.Involutive (reverseOddCycle : Perm α → Perm α) := by
  intro σ
  by_cases h : (oddLongPoints σ).Nonempty
  · have hne' : (oddLongPoints (reverseOddCycle σ)).Nonempty := by
      rwa [oddLongPoints_reverseOddCycle]
    have hmin : (oddLongPoints (reverseOddCycle σ)).min' hne' =
        (oddLongPoints σ).min' h := by
      apply le_antisymm
      · exact (isLeast_min' _ hne').2 (by
          rw [oddLongPoints_reverseOddCycle]
          exact min'_mem _ h)
      · exact (isLeast_min' _ h).2 (by
          rw [← oddLongPoints_reverseOddCycle]
          exact min'_mem _ hne')
    rw [reverseOddCycle_of_nonempty hne', hmin, reverseOddCycle_cycleOf_min h, inv_inv,
      reverseOddCycle_of_nonempty h]
    exact reverse_odd_cycle_mul_inv (odd_cycleOf_min_mem_cycleFactorsFinset h)
  · rw [reverseOddCycle_of_empty h, reverseOddCycle_of_empty h]

lemma sum_cayleyWeight_eq_sum_no_odd {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (x : α → ℂ) :
    (∑ σ : Perm α, cayleyWeight x σ) =
      ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ := by
  have hrev :
      (∑ σ : Perm α, cayleyWeight x (reverseOddCycle σ)) =
        ∑ σ : Perm α, cayleyWeight x σ :=
    Equiv.sum_comp (reverseOddCycle_involutive.toPerm reverseOddCycle) (cayleyWeight x)
  have hsum :
      (∑ σ : Perm α, (cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ))) =
        2 * ∑ σ : Perm α, cayleyWeight x σ := by
    rw [sum_add_distrib, hrev, two_mul]
  have hterm : ∀ σ : Perm α,
      cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ) =
        if (oddLongPoints σ).Nonempty then 0 else 2 * cayleyWeight x σ := by
    intro σ
    by_cases h : (oddLongPoints σ).Nonempty
    · rw [if_pos h, cayleyWeight_reverseOddCycle, if_pos h]
      ring
    · rw [if_neg h, cayleyWeight_reverseOddCycle, if_neg h]
      ring
  have hite : ∀ σ : Perm α,
      (if (oddLongPoints σ).Nonempty then (0 : ℂ) else 2 * cayleyWeight x σ) =
        2 * (if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ) := by
    intro σ
    split_ifs <;> ring
  have hsum' :
      (∑ σ : Perm α, (cayleyWeight x σ + cayleyWeight x (reverseOddCycle σ))) =
        2 * ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ := by
    rw [Fintype.sum_congr _ _ hterm, Fintype.sum_congr _ _ hite, mul_sum]
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) (hsum.symm.trans hsum')

lemma permanent_sunMatrix_eq_sum_no_odd {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent =
      ∑ σ : Perm (Fin (2 * n)),
        if (oddLongPoints σ).Nonempty then 0
        else cayleyWeight (fun i => ζ ^ i.val) σ := by
  rw [permanent_sunMatrix_eq_sum_cayleyWeight hn hζ]
  exact sum_cayleyWeight_eq_sum_no_odd _

lemma oddLongPoints_eq_empty_iff {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α} :
    oddLongPoints σ = ∅ ↔ ∀ c ∈ σ.cycleFactorsFinset, Even c.support.card := by
  rw [← not_nonempty_iff_eq_empty, oddLongPoints_nonempty_iff]
  simp only [not_exists, not_and, Nat.not_odd_iff_even]

lemma oddLongPoints_one {α : Type*} [Fintype α] [DecidableEq α] :
    oddLongPoints (1 : Perm α) = ∅ := by
  ext a
  simp [mem_oddLongPoints, Equiv.Perm.cycleOf_one, Equiv.Perm.support_one]

lemma oddLongPoints_swap {α : Type*} [Fintype α] [DecidableEq α]
    {a b : α} (h : a ≠ b) : oddLongPoints (Equiv.swap a b) = ∅ := by
  ext x
  simp only [mem_oddLongPoints]
  have hodd : ¬ Odd ((Equiv.swap a b).cycleOf x).support.card := by
    by_cases hx : x = a ∨ x = b
    · have hxsup : x ∈ (Equiv.swap a b).support := by
        rw [Equiv.Perm.support_swap h]
        simpa using hx
      have : (Equiv.swap a b).cycleOf x = Equiv.swap a b :=
        Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.isCycle_swap h)
          (Equiv.Perm.mem_support.mp hxsup)
      rw [this, Equiv.Perm.support_swap h]
      have hcard : ({a, b} : Finset α).card = 2 := by
        rw [card_insert_of_notMem (by simp [h]), card_singleton]
      simp [hcard]
    · have hxab : x ≠ a ∧ x ≠ b := by
        simp only [not_or] at hx
        exact hx
      have hfix : Equiv.swap a b x = x := swap_apply_of_ne_of_ne hxab.1 hxab.2
      have h1 : (Equiv.swap a b).cycleOf x = 1 :=
        (Equiv.Perm.cycleOf_eq_one_iff _).mpr hfix
      simp [h1, Equiv.Perm.support_one]
  simp [hodd]

lemma cayleyWeight_swap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) :
    cayleyWeight x (Equiv.swap a b) =
      (x a + x b) / (x a - x b) * ((x b + x a) / (x b - x a)) := by
  unfold cayleyWeight
  rw [Equiv.Perm.support_swap h, prod_insert (by simp [h]), prod_singleton]
  simp [swap_apply_left, swap_apply_right]

lemma cayleyWeight_swap_sq {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (h : a ≠ b) :
    cayleyWeight x (Equiv.swap a b) = - ((x a + x b) / (x a - x b)) ^ 2 := by
  rw [cayleyWeight_swap x h, cayleyFactor_swap (x a) (x b)]
  ring

lemma one_add_cayleyWeight_swap {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {a b : α} (hab : a ≠ b) (hx : x a ≠ x b) :
    1 + cayleyWeight x (Equiv.swap a b) =
      -4 * x a * x b / (x a - x b) ^ 2 := by
  have hden : x a - x b ≠ 0 := sub_ne_zero.2 hx
  rw [cayleyWeight_swap_sq x hab]
  field_simp [hden]
  ring

lemma cayleyWeight_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → Prop} [DecidablePred p] (x : α → ℂ) (u : Perm (Subtype p)) :
    cayleyWeight x (Equiv.Perm.ofSubtype u) =
      cayleyWeight (fun q : Subtype p => x q.1) u := by
  simp only [cayleyWeight, Equiv.Perm.support_ofSubtype]
  rw [prod_map]
  refine prod_congr rfl fun q _ => ?_
  simp [Equiv.Perm.ofSubtype_apply_coe]

/-- Cayley-kernel sum after odd cycles of length at least 3 have cancelled. -/
noncomputable def cayleySum {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (x : α → ℂ) : ℂ :=
  ∑ σ : Perm α, if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ

lemma permanent_sunMatrix_eq_cayleySum {n : ℕ} (hn : 1 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * n)) :
    (sunMatrix n ζ).permanent = cayleySum (fun i : Fin (2 * n) => ζ ^ i.val) :=
  permanent_sunMatrix_eq_sum_no_odd hn hζ

lemma one_ne_swap_fin_two :
    (1 : Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
  intro h
  have := congr_fun (congr_arg (fun f : Perm (Fin 2) => (f : Fin 2 → Fin 2)) h) 0
  simp at this

lemma cayleySum_fin_two (x : Fin 2 → ℂ) :
    cayleySum x = 1 + cayleyWeight x (Equiv.swap (0 : Fin 2) 1) := by
  unfold cayleySum
  rw [show (univ : Finset (Perm (Fin 2))) = {1, Equiv.swap 0 1} from
    univ_perm_fin_two]
  rw [sum_insert (by simp [one_ne_swap_fin_two]), sum_singleton]
  have h1 : ¬ (oddLongPoints (1 : Perm (Fin 2))).Nonempty := by
    simp [oddLongPoints_one]
  have hs : ¬ (oddLongPoints (Equiv.swap (0 : Fin 2) 1)).Nonempty := by
    simp [oddLongPoints_swap Fin.zero_ne_one]
  rw [if_neg h1, if_neg hs, cayleyWeight_one]

lemma cayleySum_fin_two_eq {x : Fin 2 → ℂ} (hx : x 0 ≠ x 1) :
    cayleySum x = -4 * x 0 * x 1 / (x 0 - x 1) ^ 2 := by
  rw [cayleySum_fin_two, one_add_cayleyWeight_swap x Fin.zero_ne_one hx]

lemma disjoint_swap_of_fixed {α : Type*} [DecidableEq α] {p q : α} (_hpq : p ≠ q)
    {τ : Perm α} (hp : τ p = p) (hq : τ q = q) :
    Equiv.Perm.Disjoint (Equiv.swap p q) τ := by
  intro x
  by_cases hxp : x = p
  · right
    rw [hxp, hp]
  · by_cases hxq : x = q
    · right
      rw [hxq, hq]
    · left
      exact swap_apply_of_ne_of_ne hxp hxq

lemma cycleOf_mul_swap_of_mem {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) {x : α}
    (hx : x = p ∨ x = q) :
    (Equiv.swap p q * τ).cycleOf x = Equiv.swap p q := by
  have hsw : (Equiv.swap p q).IsCycle := Equiv.Perm.isCycle_swap hpq
  have hxsup : x ∈ (Equiv.swap p q).support := by
    rw [Equiv.Perm.support_swap hpq]
    simpa using hx
  have hτx : τ x = x := by
    have := hdis x
    have hne : Equiv.swap p q x ≠ x := Equiv.Perm.mem_support.mp hxsup
    exact this.resolve_left hne
  have hmem : Equiv.swap p q ∈ (Equiv.swap p q * τ).cycleFactorsFinset := by
    rw [hdis.cycleFactorsFinset_mul_eq_union, hsw.cycleFactorsFinset_eq_singleton]
    simp
  exact (Equiv.Perm.cycle_is_cycleOf hxsup hmem).symm

lemma cycleOf_mul_swap_of_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (_hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) {x : α}
    (hx : x ≠ p ∧ x ≠ q) :
    (Equiv.swap p q * τ).cycleOf x = τ.cycleOf x := by
  have hswx : Equiv.swap p q x = x := swap_apply_of_ne_of_ne hx.1 hx.2
  have h1 : (Equiv.swap p q).cycleOf x = 1 :=
    (Equiv.Perm.cycleOf_eq_one_iff _).mpr hswx
  rw [Equiv.Perm.Disjoint.cycleOf_mul_distrib hdis x, h1, one_mul]

lemma oddLongPoints_mul_swap {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {τ : Perm α}
    (hdis : Equiv.Perm.Disjoint (Equiv.swap p q) τ) :
    oddLongPoints (Equiv.swap p q * τ) = oddLongPoints τ := by
  ext x
  simp only [mem_oddLongPoints]
  by_cases hx : x = p ∨ x = q
  · rw [cycleOf_mul_swap_of_mem hpq hdis hx, Equiv.Perm.support_swap hpq]
    have hcard : ({p, q} : Finset α).card = 2 := by
      rw [card_insert_of_notMem (by simp [hpq]), card_singleton]
    have hτx : τ x = x := by
      have hxsup : x ∈ (Equiv.swap p q).support := by
        rw [Equiv.Perm.support_swap hpq]
        simpa using hx
      have hne : Equiv.swap p q x ≠ x := Equiv.Perm.mem_support.mp hxsup
      exact (hdis x).resolve_left hne
    have h1 : τ.cycleOf x = 1 := (Equiv.Perm.cycleOf_eq_one_iff τ).mpr hτx
    simp [hcard, h1, Equiv.Perm.support_one]
  · have hxab : x ≠ p ∧ x ≠ q := by
      simp only [not_or] at hx
      exact hx
    rw [cycleOf_mul_swap_of_not_mem hpq hdis hxab]

lemma ofSubtype_zpow {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    (u : Perm (Subtype p)) (n : ℤ) :
    Equiv.Perm.ofSubtype u ^ n = Equiv.Perm.ofSubtype (u ^ n) :=
  (MonoidHom.map_zpow Equiv.Perm.ofSubtype u n).symm

lemma sameCycle_ofSubtype_coe {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x y : {a // a ∈ s}} :
    Equiv.Perm.SameCycle (Equiv.Perm.ofSubtype u) x.1 y.1 ↔
      Equiv.Perm.SameCycle u x y := by
  constructor
  · intro ⟨n, h⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [← h, ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_coe]
  · intro ⟨n, h⟩
    refine ⟨n, ?_⟩
    rw [ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_coe]
    exact congrArg Subtype.val h

lemma sameCycle_ofSubtype_mem {α : Type*} [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x y : α} (hx : x ∈ s)
    (h : Equiv.Perm.SameCycle (Equiv.Perm.ofSubtype u) x y) : y ∈ s := by
  obtain ⟨n, hxy⟩ := h
  rw [ofSubtype_zpow, Equiv.Perm.ofSubtype_apply_of_mem _ hx] at hxy
  exact hxy ▸ ((u ^ n) ⟨x, hx⟩).2

lemma support_cycleOf_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α}
    (u : Perm {a // a ∈ s}) {x : α} (hx : x ∈ s) :
    ((Equiv.Perm.ofSubtype u).cycleOf x).support =
      (u.cycleOf ⟨x, hx⟩).support.map (Function.Embedding.subtype (fun a => a ∈ s)) := by
  ext y
  simp only [Equiv.Perm.mem_support_cycleOf_iff, mem_map, Function.Embedding.coe_subtype]
  constructor
  · intro ⟨hsame, hsup⟩
    have hy : y ∈ s := sameCycle_ofSubtype_mem u hx hsame
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    constructor
    · exact (sameCycle_ofSubtype_coe u).1 hsame
    · have hne : Equiv.Perm.ofSubtype u x ≠ x := Equiv.Perm.mem_support.mp hsup
      exact Equiv.Perm.mem_support.mpr fun h =>
        hne (by
          rw [Equiv.Perm.ofSubtype_apply_of_mem u hx]
          exact congrArg Subtype.val h)
  · intro ⟨z, hmem, hz⟩
    subst hz
    constructor
    · exact (sameCycle_ofSubtype_coe u).2 hmem.1
    · have hne : u ⟨x, hx⟩ ≠ ⟨x, hx⟩ := Equiv.Perm.mem_support.mp hmem.2
      exact Equiv.Perm.mem_support.mpr fun h =>
        hne (Subtype.ext (by
          rw [← Equiv.Perm.ofSubtype_apply_of_mem u hx]
          exact h))

lemma oddLongPoints_ofSubtype_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset α} (u : Perm {a // a ∈ s}) :
    (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty ↔
      (oddLongPoints u).Nonempty := by
  constructor
  · intro ⟨x, hx⟩
    rw [mem_oddLongPoints] at hx
    have hmove : Equiv.Perm.ofSubtype u x ≠ x := odd_card_cycleOf_ne_self hx
    have hxs : x ∈ s := by
      by_contra hns
      exact hmove (Equiv.Perm.ofSubtype_apply_of_not_mem u hns)
    refine ⟨⟨x, hxs⟩, mem_oddLongPoints.mpr ?_⟩
    rw [support_cycleOf_ofSubtype u hxs, card_map] at hx
    exact hx
  · intro ⟨⟨x, hxs⟩, hx⟩
    rw [mem_oddLongPoints] at hx
    refine ⟨x, mem_oddLongPoints.mpr ?_⟩
    rwa [support_cycleOf_ofSubtype u hxs, card_map]

lemma cayleySum_ofSubtype {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {s : Finset α} (x : α → ℂ) (u : Perm {a // a ∈ s}) :
    (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.Perm.ofSubtype u)) =
      if (oddLongPoints u).Nonempty then 0
      else cayleyWeight (fun a : {a // a ∈ s} => x a.1) u := by
  by_cases h : (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty
  · have h' : (oddLongPoints u).Nonempty :=
      (oddLongPoints_ofSubtype_nonempty_iff u).1 h
    simp [h, h']
  · have h' : ¬ (oddLongPoints u).Nonempty := fun hne =>
      h ((oddLongPoints_ofSubtype_nonempty_iff u).2 hne)
    rw [if_neg h, if_neg h']
    convert cayleyWeight_ofSubtype (p := fun a => a ∈ s) x u

/-- Cayley-kernel even-cycle sum on a subset. -/
noncomputable def cayleySumOn {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (s : Finset α) (x : α → ℂ) : ℂ :=
  cayleySum (fun a : {a // a ∈ s} => x a.1)

lemma ofSubtype_fixes_pair {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    Equiv.Perm.ofSubtype u p = p ∧ Equiv.Perm.ofSubtype u q = q := by
  constructor
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)

lemma disjoint_swap_ofSubtype_pair {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    Equiv.Perm.Disjoint (Equiv.swap p q) (Equiv.Perm.ofSubtype u) :=
  disjoint_swap_of_fixed hpq (ofSubtype_fixes_pair u).1 (ofSubtype_fixes_pair u).2

lemma swap_mul_ofSubtype_apply {α : Type*} [Fintype α] [DecidableEq α] {p q : α}
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u) p = q := by
  change Equiv.swap p q (Equiv.Perm.ofSubtype u p) = q
  rw [(ofSubtype_fixes_pair u).1, swap_apply_left]

lemma cycleOf_swap_mul_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (Equiv.swap p q * Equiv.Perm.ofSubtype u).cycleOf p = Equiv.swap p q :=
  cycleOf_mul_swap_of_mem hpq (disjoint_swap_ofSubtype_pair hpq u) (Or.inl rfl)

lemma cayleySum_term_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {p q : α} (hpq : p ≠ q) (x : α → ℂ)
    (u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ}) :
    (if (oddLongPoints (Equiv.swap p q * Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u)) =
      cayleyWeight x (Equiv.swap p q) *
        (if (oddLongPoints u).Nonempty then 0
          else cayleyWeight (fun a : {a // a ∈ ({p, q} : Finset α)ᶜ} => x a.1) u) := by
  have hdis := disjoint_swap_ofSubtype_pair hpq u
  rw [oddLongPoints_mul_swap hpq hdis, cayleyWeight_mul_disjoint x hdis]
  have hfac :
      (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
        else cayleyWeight x (Equiv.swap p q) *
          cayleyWeight x (Equiv.Perm.ofSubtype u)) =
        cayleyWeight x (Equiv.swap p q) *
          (if (oddLongPoints (Equiv.Perm.ofSubtype u)).Nonempty then 0
            else cayleyWeight x (Equiv.Perm.ofSubtype u)) := by
    split_ifs <;> ring
  rw [hfac]
  exact congrArg (fun t => cayleyWeight x (Equiv.swap p q) * t) (cayleySum_ofSubtype x u)

lemma sum_cayleySum_term_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] {p q : α} (hpq : p ≠ q) (x : α → ℂ) :
    (∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
      if (oddLongPoints (Equiv.swap p q * Equiv.Perm.ofSubtype u)).Nonempty then (0 : ℂ)
      else cayleyWeight x (Equiv.swap p q * Equiv.Perm.ofSubtype u)) =
      cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x := by
  simp_rw [cayleySum_term_swap_ofSubtype hpq x]
  rw [← mul_sum]
  rfl

lemma ne_of_cycleOf_support_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (h : (σ.cycleOf p).support.card = 2) : σ p ≠ p := by
  intro hfix
  have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
  have h0 : (σ.cycleOf p).support.card = 0 := by
    rw [h1, Equiv.Perm.support_one, card_empty]
  omega

lemma cycleOf_eq_swap_of_card_two {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {p : α} (h : (σ.cycleOf p).support.card = 2) :
    σ.cycleOf p = Equiv.swap p (σ p) := by
  have hp := ne_of_cycleOf_support_card_two h
  have hf : Equiv.Perm.IsSwap (σ.cycleOf p) :=
    (Equiv.Perm.card_support_eq_two).mp h
  obtain ⟨a, b, hab, heq⟩ := hf
  have hp_mem : p ∈ (σ.cycleOf p).support :=
    Equiv.Perm.mem_support.mpr (by
      rw [Equiv.Perm.cycleOf_apply_self σ p]
      exact hp)
  have hpab : p = a ∨ p = b := by
    rw [heq, Equiv.Perm.support_swap hab, mem_insert, mem_singleton] at hp_mem
    exact hp_mem
  have happ : (σ.cycleOf p) p = σ p := Equiv.Perm.cycleOf_apply_self σ p
  rcases hpab with hpa | hpb
  · subst hpa
    have hb : b = σ p := by
      rw [heq, swap_apply_left] at happ
      exact happ
    rw [heq, hb]
  · subst hpb
    have ha : a = σ p := by
      rw [heq, swap_apply_right] at happ
      exact happ
    rw [heq, ha, Equiv.swap_comm]

lemma swap_mem_cycleFactors_of_cycleOf {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    Equiv.swap p q ∈ σ.cycleFactorsFinset := by
  have hp : p ∈ σ.support := by
    rw [Equiv.Perm.mem_support]
    have happ := Equiv.Perm.cycleOf_apply_self σ p
    rw [h, swap_apply_left] at happ
    exact happ ▸ hpq.symm
  have hmem : σ.cycleOf p ∈ σ.cycleFactorsFinset :=
    (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff).2 hp
  rwa [h] at hmem

lemma remainder_support_subset_cycle_compl {α : Type*} [Fintype α] [DecidableEq α]
    {σ c : Perm α} (hc : c ∈ σ.cycleFactorsFinset) :
    (σ * c⁻¹).support ⊆ c.supportᶜ := by
  intro x hx
  rw [mem_compl]
  intro hxmem
  exact (Equiv.Perm.notMem_support.mpr (remainder_apply_eq_self_of_mem hc hxmem)) hx

lemma eq_swap_mul_remainder {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    σ = Equiv.swap p q * (σ * Equiv.swap p q) := by
  have hσeq := eq_mul_remainder_of_mem_cycleFactorsFinset
    (swap_mem_cycleFactors_of_cycleOf hpq h)
  rwa [Equiv.swap_inv] at hσeq

lemma exists_eq_swap_mul_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) {σ : Perm α} (h : σ.cycleOf p = Equiv.swap p q) :
    ∃ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
      σ = Equiv.swap p q * Equiv.Perm.ofSubtype u := by
  have hc := swap_mem_cycleFactors_of_cycleOf hpq h
  have hsub : (σ * Equiv.swap p q).support ⊆ ({p, q} : Finset α)ᶜ := by
    have hrem : (σ * (Equiv.swap p q)⁻¹).support ⊆ (Equiv.swap p q).supportᶜ :=
      remainder_support_subset_cycle_compl hc
    rwa [Equiv.swap_inv, Equiv.Perm.support_swap hpq] at hrem
  refine ⟨(σ * Equiv.swap p q).subtypePerm fun x =>
      (mem_of_support_subset hsub x).symm, ?_⟩
  have hrec := ofSubtype_subtypePerm_of_support_subset hsub
  rw [hrec]
  exact eq_swap_mul_remainder hpq h

lemma swap_eq_swap_iff_right {α : Type*} [DecidableEq α] {p q q' : α}
    (_hpq : p ≠ q) (h : Equiv.swap p q = Equiv.swap p q') : q = q' := by
  have := congr_fun (congr_arg (fun f : Perm α => (f : α → α)) h) p
  simpa [swap_apply_left] using this

noncomputable def equiv_remainder_of_swap_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) :
    Perm {a // a ∈ ({p, q} : Finset α)ᶜ} ≃
      {σ : Perm α // σ.cycleOf p = Equiv.swap p q} :=
  Equiv.ofBijective
    (fun u => ⟨Equiv.swap p q * Equiv.Perm.ofSubtype u, cycleOf_swap_mul_ofSubtype hpq u⟩)
    ⟨fun u v h =>
        Equiv.Perm.ofSubtype_injective (mul_left_cancel (congrArg Subtype.val h)),
      fun σ => by
        obtain ⟨u, hu⟩ := exists_eq_swap_mul_ofSubtype hpq σ.2
        exact ⟨u, Subtype.ext hu.symm⟩⟩

lemma sum_fiber_swap_ofSubtype {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α} (hpq : p ≠ q) (f : Perm α → ℂ) :
    (∑ σ : Perm α, if σ.cycleOf p = Equiv.swap p q then f σ else 0) =
      ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
        f (Equiv.swap p q * Equiv.Perm.ofSubtype u) := by
  have hsub :
      (∑ σ ∈ univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q), f σ) =
        ∑ σ : {σ : Perm α // σ.cycleOf p = Equiv.swap p q}, f σ.1 :=
    sum_subtype (univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q))
      (fun σ => by simp) f
  calc (∑ σ : Perm α, if σ.cycleOf p = Equiv.swap p q then f σ else 0)
      = ∑ σ ∈ univ.filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q), f σ :=
        (sum_filter (fun σ : Perm α => σ.cycleOf p = Equiv.swap p q) f).symm
    _ = ∑ σ : {σ : Perm α // σ.cycleOf p = Equiv.swap p q}, f σ.1 := hsub
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          f (equiv_remainder_of_swap_cycle hpq u).1 :=
        (Equiv.sum_comp (equiv_remainder_of_swap_cycle hpq) (fun σ => f σ.1)).symm
    _ = ∑ u : Perm {a // a ∈ ({p, q} : Finset α)ᶜ},
          f (Equiv.swap p q * Equiv.Perm.ofSubtype u) :=
        rfl

lemma cayleySum_sigma2 {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if (σ.cycleOf p).support.card = 2 then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      ∑ q : α, if q = p then 0 else
        cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x := by
  have hsplit : ∀ σ : Perm α,
      (if (σ.cycleOf p).support.card = 2 then
        (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
      else 0) =
        ∑ q : α, if q = p then 0 else
          if σ.cycleOf p = Equiv.swap p q then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0 := by
    intro σ
    by_cases hcard : (σ.cycleOf p).support.card = 2
    · have hp := ne_of_cycleOf_support_card_two hcard
      have hcy := cycleOf_eq_swap_of_card_two hcard
      rw [if_pos hcard]
      have hsum :
          (∑ q : α, if q = p then (0 : ℂ) else
            if σ.cycleOf p = Equiv.swap p q then
              (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
            else 0) =
            if σ p = p then (0 : ℂ) else
              if σ.cycleOf p = Equiv.swap p (σ p) then
                (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
              else 0 :=
        Fintype.sum_eq_single (σ p) fun q hq => by
          by_cases hqp : q = p
          · simp [hqp]
          · have hne : σ.cycleOf p ≠ Equiv.swap p q := fun hsw =>
              hq (swap_eq_swap_iff_right (p := p) hp.symm (hcy.symm.trans hsw)).symm
            simp [hqp, hne]
      rw [hsum]
      simp [hp, hcy]
    · rw [if_neg hcard]
      refine (sum_eq_zero fun q _ => ?_).symm
      by_cases hpq : q = p
      · simp [hpq]
      · have hpq' : p ≠ q := fun h => hpq h.symm
        simp only [hpq, ↓reduceIte]
        by_cases hcy : σ.cycleOf p = Equiv.swap p q
        · exact (hcard (by simp [hcy, Equiv.Perm.card_support_swap hpq'])).elim
        · simp [hcy]
  refine (Fintype.sum_congr _ _ hsplit).trans ?_
  rw [sum_comm]
  refine Fintype.sum_congr _ _ fun q => ?_
  by_cases hpq : q = p
  · simp [hpq]
  · have hpq' : p ≠ q := fun h => hpq h.symm
    simp only [hpq, ↓reduceIte]
    rw [sum_fiber_swap_ofSubtype hpq'
      (fun σ => if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)]
    exact sum_cayleySum_term_swap_ofSubtype hpq' x

/-- She–Sun–Xia (2.4). -/
lemma cayley_triple_identity (x y z : ℂ)
    (hyz : y + z ≠ 0) (hxz : x ≠ z) (hyx : y ≠ x) :
    (y - z) / (y + z) * (x + z) / (x - z) * (y + x) / (y - x) =
      (z - y) / (z + y) + 2 * x * ((x - z)⁻¹ - (x - y)⁻¹) := by
  have hyx0 : y - x ≠ 0 := sub_ne_zero.2 hyx
  have hxz0 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have hzy : z + y ≠ 0 := by rw [add_comm]; exact hyz
  field_simp [hyz, hyx0, hxz0, hzy]
  ring

lemma cayleyWeight_formPerm {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℂ) {l : List α} (hl : l.Nodup) (h2 : 2 ≤ l.length) :
    cayleyWeight x l.formPerm =
      ∏ i : Fin l.length,
        (x (l[i.val]) +
            x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega)))) /
        (x (l[i.val]) -
            x (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (by omega)))) := by
  have hne : ∀ a : α, l ≠ [a] := by
    intro a h
    simp [h] at h2
  rw [cayleyWeight, List.support_formPerm_of_nodup l hl hne, prod_toFinset_getElem hl]
  refine prod_congr rfl fun i _ => ?_
  rw [List.formPerm_apply_getElem l hl i.val i.isLt]

lemma support_subset_compl_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    {p : α} {σ : Perm α} (h : σ p = p) : σ.support ⊆ ({p} : Finset α)ᶜ := by
  intro x hx
  rw [mem_compl, mem_singleton]
  intro hxp
  subst hxp
  exact Equiv.Perm.mem_support.mp hx h

noncomputable def equiv_remainder_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) : Perm {a // a ∈ ({p} : Finset α)ᶜ} ≃ {σ : Perm α // σ p = p} :=
  Equiv.ofBijective
    (fun u => ⟨Equiv.Perm.ofSubtype u, Equiv.Perm.ofSubtype_apply_of_not_mem u (by simp)⟩)
    ⟨fun u v h => Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h),
      fun σ => by
        have hsub : σ.1.support ⊆ ({p} : Finset α)ᶜ :=
          support_subset_compl_of_fixed σ.2
        refine ⟨σ.1.subtypePerm fun x => (mem_of_support_subset hsub x).symm, ?_⟩
        exact Subtype.ext (ofSubtype_subtypePerm_of_support_subset hsub)⟩

lemma sum_fiber_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (f : Perm α → ℂ) :
    (∑ σ : Perm α, if σ p = p then f σ else 0) =
      ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ}, f (Equiv.Perm.ofSubtype u) := by
  have hsub :
      (∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p), f σ) =
        ∑ σ : {σ : Perm α // σ p = p}, f σ.1 :=
    sum_subtype (univ.filter (fun σ : Perm α => σ p = p)) (fun σ => by simp) f
  calc (∑ σ : Perm α, if σ p = p then f σ else 0)
      = ∑ σ ∈ univ.filter (fun σ : Perm α => σ p = p), f σ :=
        (sum_filter (fun σ : Perm α => σ p = p) f).symm
    _ = ∑ σ : {σ : Perm α // σ p = p}, f σ.1 := hsub
    _ = ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ},
          f (equiv_remainder_of_fixed p u).1 :=
        (Equiv.sum_comp (equiv_remainder_of_fixed p) (fun σ => f σ.1)).symm
    _ = ∑ u : Perm {a // a ∈ ({p} : Finset α)ᶜ}, f (Equiv.Perm.ofSubtype u) :=
        rfl

lemma cayleySum_sigma1 {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    (∑ σ : Perm α,
        if σ p = p then
          (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
        else 0) =
      cayleySumOn ({p} : Finset α)ᶜ x := by
  rw [sum_fiber_fixed p
    (fun σ => if (oddLongPoints σ).Nonempty then 0 else cayleyWeight x σ)]
  exact Fintype.sum_congr _ _ fun u => cayleySum_ofSubtype x u

lemma cayleySum_split {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (p : α) (x : α → ℂ) :
    cayleySum x =
      (∑ σ : Perm α,
          if σ p = p then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) +
      (∑ σ : Perm α,
          if (σ.cycleOf p).support.card = 2 then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) +
      (∑ σ : Perm α,
          if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) := by
  unfold cayleySum
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine Fintype.sum_congr _ _ fun σ => ?_
  by_cases hp : σ p = p
  · have h0 : (σ.cycleOf p).support.card = 0 := by
      have h1 : σ.cycleOf p = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hp
      rw [h1, Equiv.Perm.support_one, card_empty]
    have h2 : ¬ (σ.cycleOf p).support.card = 2 := by omega
    have h4 : ¬ 4 ≤ (σ.cycleOf p).support.card := by omega
    simp [hp, h2, h4]
  · have hcard : 2 ≤ (σ.cycleOf p).support.card :=
      Equiv.Perm.IsCycle.two_le_card_support (Equiv.Perm.isCycle_cycleOf σ hp)
    by_cases h2 : (σ.cycleOf p).support.card = 2
    · simp [hp, h2]
    · by_cases h4 : 4 ≤ (σ.cycleOf p).support.card
      · simp [hp, h2, h4]
      · have h3 : (σ.cycleOf p).support.card = 3 := by omega
        have hodd : (oddLongPoints σ).Nonempty := by
          refine ⟨p, mem_oddLongPoints.mpr ?_⟩
          rw [h3]
          exact ⟨1, rfl⟩
        simp [hp, h2, h4, hodd]

lemma cayleySum_eq_sigma1_add_sigma2_add {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (p : α) (x : α → ℂ) :
    cayleySum x =
      cayleySumOn ({p} : Finset α)ᶜ x +
      (∑ q : α, if q = p then 0 else
        cayleyWeight x (Equiv.swap p q) * cayleySumOn ({p, q} : Finset α)ᶜ x) +
      (∑ σ : Perm α,
          if 4 ≤ (σ.cycleOf p).support.card then
            (if (oddLongPoints σ).Nonempty then (0 : ℂ) else cayleyWeight x σ)
          else 0) := by
  rw [cayleySum_split p x, cayleySum_sigma1 p x, cayleySum_sigma2 p x]

#check (OeisA1818.conjecture1 :
    ∀ (n : ℕ), 1 ≤ n → ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      (sunMatrix n ζ).permanent = (a n : ℂ))

#print axioms conjecture1_of_one
#print axioms zpow_sub_ne_one
#print axioms inv_one_sub_eq_sum
#print axioms denom_ne_zero
#print axioms calogero_kernel_sum
#print axioms det_calogero
#print axioms prod_zeta_perm
#print axioms sunMatrix_sub_ones_off
#print axioms permanent_of_zero_diag
#print axioms det_of_zero_diag
#print axioms det_calogero_eq_signed_sum
#print axioms permanent_sunMatrix_sub_ones
#print axioms signed_derangement_inv_sum
#print axioms two_three_cycles_cancel
#print axioms sum_insert_kernel
#print axioms cycleEdgeWeight_formPerm
#print axioms cycleEdgeWeight_mul_disjoint
#print axioms cycleEdgeWeight_formPerm_cons
#print axioms sum_cycleEdgeWeight_cons_rotate
#print axioms ofFn_rotate
#print axioms sum_cycleEdgeWeight_ncycles
#print axioms zeta_pow_sub
#print axioms cycleEdgeWeight_zeta
#print axioms listing_isCycle
#print axioms listing_support_univ
#print axioms listing_inv_one_sub_sum
#print axioms cycleEdgeWeight_zeta_univ
#print axioms ncycleToListingFun_injective
#print axioms ncycleToListingFun_surjective
#print axioms ncycleToListing_listingPerm
#print axioms listingPerm_ncycleToListing
#print axioms ncycle_inv_one_sub_sum
#print axioms cycleEdgeWeight_ofSubtype
#print axioms ofSubtype_isCycle
#print axioms sum_cycleEdgeWeight_replace_cycle
#print axioms coe_units_neg_one_pow
#print axioms sign_of_cycleType_replicate_two
#print axioms cycleType_eq_replicate_two
#print axioms derangement_long_cycle_or_replicate_two
#print axioms inv_one_sub_prod_of_univ
#print axioms involution_unsigned_eq_neg_signed
#print axioms ofSubtype_subtypePerm_of_support_subset
#print axioms support_ofSubtype_listing
#print axioms support_mul_listing_τ
#print axioms inv_one_sub_replace_cycle
#print axioms longPoints_nonempty_iff
#print axioms remainder_support_eq_compl
#print axioms ofSubtype_mul_remainder
#print axioms cycleOf_mul_listing
#print axioms longPoints_mul_listing
#print axioms sum_eq_sum_longKey
#print axioms longKey_of_listing
#print axioms isCycle_subtypePerm_of_support
#print axioms eq_listing_of_longKey
#print axioms long_fiber_inv_one_sub
#print axioms long_cycle_inv_one_sub_sum
#print axioms long_fiber_signed_inv_one_sub
#print axioms long_cycle_signed_inv_one_sub_sum
#print axioms unsigned_derangement_inv_sum
#print axioms permanent_sunMatrix_sub_ones_eq_a
#print axioms cayleyWeight_inv
#print axioms prod_sunMatrix_eq_cayleyWeight
#print axioms permanent_sunMatrix_eq_sum_cayleyWeight
#print axioms cayleyWeight_reverse_odd_cycle
#print axioms reverseOddCycle_involutive
#print axioms sum_cayleyWeight_eq_sum_no_odd
#print axioms permanent_sunMatrix_eq_sum_no_odd
#print axioms one_add_cayleyWeight_swap
#print axioms cayleySum_fin_two_eq
#print axioms cayleyWeight_ofSubtype
#print axioms oddLongPoints_mul_swap
#print axioms oddLongPoints_ofSubtype_nonempty_iff
#print axioms cayleySum_ofSubtype
#print axioms cayleySum_term_swap_ofSubtype
#print axioms sum_cayleySum_term_swap_ofSubtype
#print axioms cycleOf_eq_swap_of_card_two
#print axioms exists_eq_swap_mul_ofSubtype
#print axioms sum_fiber_swap_ofSubtype
#print axioms cayleySum_sigma2
#print axioms cayley_triple_identity
#print axioms cayleyWeight_formPerm
#print axioms sum_fiber_fixed
#print axioms cayleySum_sigma1
#print axioms cayleySum_split
#print axioms cayleySum_eq_sigma1_add_sigma2_add

end A001818C1
