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

/- Type of the frozen source theorem, with `sunMatrix` in place of the inline matrix. -/
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

end A001818C1
