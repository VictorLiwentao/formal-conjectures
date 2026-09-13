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
Prior exact Lean proof: Kenta Kitamura (KitaKen1), July 2026.
This independent implementation and write-up: Wentao Li.
-/
import FormalConjecturesUtil

/-!
A later independent Lean implementation of Chung's induced-path bound,
matching WOWII Graph Conjecture 31. This is not the first exact Lean proof.

Mathematics: P. Erdős, M. Saks, V. T. Sós, Maximum induced trees in graphs,
J. Combin. Theory Ser. B 41 (1986) 61-79, Theorem 2.2. The published proof
was supplied by Fan Chung.

Prior exact Lean proof, Kenta Kitamura (KitaKen1), 2026-07-28, linked from
DeepMind PR 4658:
https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean

This file does not import WrittenOnTheWallII.GraphConjecture31 and does not
use that sorry theorem. It is a later implementation of the same type, written
without using Kitamura's source as a proof.

Classification: known_mathematics_formalization, not new mathematics.
Not a first formalization.
-/

set_option linter.unusedSectionVars false
set_option linter.style.moduleDocstring false

open SimpleGraph

namespace WOWII31

section PathNumber

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma isInducedPath_nil (G : SimpleGraph V) : isInducedPath G [] :=
  ⟨List.nodup_nil, fun i => i.elim0⟩

lemma isInducedPath_singleton (G : SimpleGraph V) (v : V) :
    isInducedPath G [v] := by
  constructor
  · simp
  · intro i j
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
    have hij : i = j := Fin.ext (hi.trans hj.symm)
    subst hij
    simp [SimpleGraph.irrefl]

lemma max_getD_eq_max' {s : Finset ℕ} (hne : s.Nonempty) :
    s.max.getD 0 = s.max' hne := by
  rw [show s.max = some (s.max' hne) from (Finset.coe_max' hne).symm]
  rfl

lemma le_path_of_isInducedPath (G : SimpleGraph V) {l : List V}
    (hl : isInducedPath G l) : l.length ≤ path G := by
  classical
  let S : Finset (Finset V) :=
    Finset.univ.filter fun s => ∃ t : List V, t.toFinset = s ∧ isInducedPath G t
  have hS : l.toFinset ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, rfl, hl⟩
  have hc : l.toFinset.card ∈ S.image Finset.card :=
    Finset.mem_image.mpr ⟨l.toFinset, hS, rfl⟩
  have hne : (S.image Finset.card).Nonempty := ⟨_, hc⟩
  have hlen : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl.1
  rw [path, max_getD_eq_max' hne, ← hlen]
  exact Finset.le_max' _ _ hc

lemma isInducedPath_map {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : H ↪g G) {l : List W}
    (hl : isInducedPath H l) : isInducedPath G (l.map f) := by
  obtain ⟨hnodup, hadj⟩ := hl
  refine ⟨hnodup.map f.injective, ?_⟩
  intro i j
  have hi : i.val < l.length := by simpa using i.isLt
  have hj : j.val < l.length := by simpa using j.isLt
  have hgeti : (l.map f).get i = f (l.get ⟨i.val, hi⟩) := by
    simp [List.get_eq_getElem, List.getElem_map]
  have hgetj : (l.map f).get j = f (l.get ⟨j.val, hj⟩) := by
    simp [List.get_eq_getElem, List.getElem_map]
  rw [hgeti, hgetj, f.map_adj_iff]
  exact hadj ⟨i.val, hi⟩ ⟨j.val, hj⟩

lemma exists_isInducedPath_length_eq_path (G : SimpleGraph V) :
    ∃ l : List V, isInducedPath G l ∧ l.length = path G := by
  classical
  let S : Finset (Finset V) :=
    Finset.univ.filter fun s => ∃ t : List V, t.toFinset = s ∧ isInducedPath G t
  let I := S.image Finset.card
  by_cases hI : I.Nonempty
  · have hmem : I.max' hI ∈ I := I.max'_mem hI
    obtain ⟨s, hs, hscard⟩ := Finset.mem_image.mp hmem
    obtain ⟨l, hls, hl⟩ := (Finset.mem_filter.mp hs).2
    refine ⟨l, hl, ?_⟩
    have hlen : l.length = s.card := by
      rw [← hls, List.toFinset_card_of_nodup hl.1]
    rw [path, max_getD_eq_max' hI, hlen, hscard]
  · refine ⟨[], isInducedPath_nil G, ?_⟩
    have hempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hmax : I.max = none := Finset.max_eq_bot.mpr hempty
    have hpath : path G = I.max.getD 0 := rfl
    simp [hpath, hmax]

lemma path_le_of_embedding {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : H ↪g G) :
    path H ≤ path G := by
  obtain ⟨l, hl, hlen⟩ := exists_isInducedPath_length_eq_path H
  have := le_path_of_isInducedPath G (isInducedPath_map f hl)
  simpa [hlen] using this

lemma path_induce_le (G : SimpleGraph V) (s : Set V) [Fintype s] [DecidableEq s] :
    path (G.induce s) ≤ path G :=
  path_le_of_embedding (Embedding.induce s)

lemma one_le_path_of_nonempty (G : SimpleGraph V) [Nonempty V] : 1 ≤ path G := by
  inhabit V
  simpa using le_path_of_isInducedPath G (isInducedPath_singleton G default)

lemma int_two_mul_sub_one_le {r n : ℕ} (h : 2 * r ≤ n + 1) :
    2 * (r : ℤ) - 1 ≤ (n : ℤ) := by omega

end PathNumber

section Dist

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma dist_le_of_hom {W : Type*} {H : SimpleGraph W}
    (f : H →g G) {x y : W} (h : H.Reachable x y) :
    G.dist (f x) (f y) ≤ H.dist x y := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  simpa [Walk.length_map, hp] using dist_le (p.map f)

lemma dist_le_induce (s : Set V) (x y : s)
    (h : (G.induce s).Reachable x y) :
    G.dist x.val y.val ≤ (G.induce s).dist x y :=
  dist_le_of_hom (Embedding.induce s).toHom h

lemma dist_take_le {u v : V} (p : G.Walk u v) (i : ℕ) :
    G.dist u (p.getVert i) ≤ min i p.length := by
  simpa [Walk.take_length] using dist_le (p.take i)

lemma dist_drop_le {u v : V} (p : G.Walk u v) (j : ℕ) :
    G.dist (p.getVert j) v ≤ p.length - j := by
  simpa [Walk.drop_length] using dist_le (p.drop j)

lemma dist_getVert {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hij : i + (j - i) = j := by omega
  have hi' : i ≤ p.length := le_trans hi hj
  have hminij : min (j - i) (p.length - i) = j - i := by omega
  have hle : G.dist (p.getVert i) (p.getVert j) ≤ j - i := by
    have := dist_le ((p.drop i).take (j - i))
    simp only [Walk.take_length, Walk.drop_length, hminij, Walk.drop_getVert, hij] at this
    exact this
  have hql : (p.drop i).getVert (j - i) = p.getVert j := by
    simp [Walk.drop_getVert, hij]
  have r1 : G.Reachable u (p.getVert i) := (p.take i).reachable
  have r2 : G.Reachable (p.getVert i) (p.getVert j) :=
    (((p.drop i).take (j - i)).copy rfl hql).reachable
  have hui : G.dist u (p.getVert i) ≤ i := by
    simpa [Nat.min_eq_left hi'] using dist_take_le p i
  have hvj : G.dist (p.getVert j) v ≤ G.dist u v - j := by
    have := dist_drop_le p j
    omega
  have h1 := r1.dist_triangle_left v
  have h2 := r2.dist_triangle_left v
  omega

lemma dist_start_getVert {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) {k : ℕ} (hk : k ≤ p.length) :
    G.dist u (p.getVert k) = k := by
  simpa using dist_getVert p hlen (Nat.zero_le k) hk

lemma dist_getVert_end {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) {k : ℕ} (hk : k ≤ p.length) :
    G.dist (p.getVert k) v = p.length - k := by
  simpa using dist_getVert p hlen hk le_rfl

lemma not_adj_nonconsecutive_geodesic {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : j ≤ p.length) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hi : i ≤ p.length := by omega
  let q := ((p.take i).concat hadj).append (p.drop j)
  have hq : q.length = i + 1 + (p.length - j) := by
    have htake : (p.take i).length = i := by simp [Walk.take_length, hi]
    simp [q, Walk.length_append, Walk.length_concat, htake, Walk.drop_length]
  have : G.dist u v ≤ q.length := dist_le q
  omega

lemma isInducedPath_of_walk {u v : V} (p : G.Walk u v)
    (hnodup : p.support.Nodup)
    (hchord : ∀ i j : ℕ, i + 2 ≤ j → j ≤ p.length → ¬ G.Adj (p.getVert i) (p.getVert j)) :
    isInducedPath G p.support := by
  refine ⟨hnodup, ?_⟩
  intro i j
  have hlenp : p.support.length = p.length + 1 := p.length_support
  have hi : i.val ≤ p.length := by have := i.isLt; omega
  have hj : j.val ≤ p.length := by have := j.isLt; omega
  have hgeti : p.support.get i = p.getVert i.val :=
    (p.getVert_eq_support_getElem hi).symm
  have hgetj : p.support.get j = p.getVert j.val :=
    (p.getVert_eq_support_getElem hj).symm
  constructor
  · intro hadj
    rw [hgeti, hgetj] at hadj
    have hne : i.val ≠ j.val := by
      intro h
      have : p.getVert i.val = p.getVert j.val := by simp [h]
      exact hadj.ne this
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · have : ¬ (i.val + 2 ≤ j.val) := fun h2 => hchord i.val j.val h2 hj hadj
      omega
    · exact (hne heq).elim
    · have : ¬ (j.val + 2 ≤ i.val) := fun h2 => hchord j.val i.val h2 hi hadj.symm
      omega
  · intro hcons
    rcases hcons with h | h
    · have : i.val < p.length := by have := j.isLt; omega
      rw [hgeti, hgetj, ← h]
      exact p.adj_getVert_succ this
    · have : j.val < p.length := by have := i.isLt; omega
      rw [hgeti, hgetj, ← h]
      exact (p.adj_getVert_succ this).symm

lemma isInducedPath_support_of_geodesic {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) : isInducedPath G p.support :=
  isInducedPath_of_walk p (p.isPath_of_length_eq_dist hlen).support_nodup
    (fun _i _j hij hj => not_adj_nonconsecutive_geodesic p hlen hij hj)

lemma getVert_injective_of_geodesic {u v : V} (p : G.Walk u v)
    (hlen : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (heq : p.getVert i = p.getVert j) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi heq.symm (le_of_not_ge hij)).symm
  have := dist_getVert p hlen hij hj
  simp [heq] at this
  omega

lemma radius_eq_natCast (hG : G.Connected) :
    G.radius = (G.radius.toNat : ℕ∞) := by
  have : Nonempty V := hG.nonempty
  exact (ENat.natCast_toNat ((radius_ne_top_iff (α := V)).mpr hG)).symm

lemma eccent_ne_top_of_connected (hG : G.Connected) (u : V) :
    G.eccent u ≠ ⊤ := by
  have : Nonempty V := hG.nonempty
  exact ne_top_of_le_ne_top ((connected_iff_ediam_ne_top (α := V)).mp hG)
    (eccent_le_ediam (u := u))

lemma radius_le_eccent_toNat (hG : G.Connected) (u : V) :
    G.radius.toNat ≤ (G.eccent u).toNat :=
  ENat.toNat_le_toNat radius_le_eccent (eccent_ne_top_of_connected hG u)

lemma exists_dist_eq_eccent (hG : G.Connected) (u : V) :
    ∃ w, G.dist u w = (G.eccent u).toNat := by
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  have hr : G.Reachable u w := hG u w
  have hcoe : (G.dist u w : ℕ∞) = G.eccent u := hr.coe_dist_eq_edist.trans hw
  exact ⟨w, (ENat.toNat_natCast (G.dist u w)).symm.trans (congrArg ENat.toNat hcoe)⟩

lemma dist_v0_le_of_center {vr : V}
    (hH : (G.induce ({vr}ᶜ : Set V)).Connected)
    {v0 : {x : V // x ≠ vr}}
    (hv0 : (G.induce ({vr}ᶜ : Set V)).eccent v0 =
      (G.induce ({vr}ᶜ : Set V)).radius)
    {x : V} (hx : x ≠ vr) :
    G.dist v0.val x ≤ ((G.induce ({vr}ᶜ : Set V)).radius).toNat := by
  have hreach : (G.induce ({vr}ᶜ : Set V)).Reachable v0 ⟨x, hx⟩ := hH v0 ⟨x, hx⟩
  have hdist := dist_le_induce (G := G) ({vr}ᶜ) v0 ⟨x, hx⟩ hreach
  have hle : (G.induce ({vr}ᶜ : Set V)).dist v0 ⟨x, hx⟩ ≤
      ((G.induce ({vr}ᶜ : Set V)).eccent v0).toNat := by
    have h1 : (G.induce ({vr}ᶜ : Set V)).edist v0 ⟨x, hx⟩ ≤
        (G.induce ({vr}ᶜ : Set V)).eccent v0 := edist_le_eccent
    have := ENat.toNat_le_toNat h1 (eccent_ne_top_of_connected hH v0)
    have hcoe := hreach.coe_dist_eq_edist
    have : ((G.induce ({vr}ᶜ : Set V)).dist v0 ⟨x, hx⟩ : ℕ∞) =
        (G.induce ({vr}ᶜ : Set V)).edist v0 ⟨x, hx⟩ := hcoe
    have hnat := congrArg ENat.toNat this
    rw [ENat.toNat_natCast] at hnat
    omega
  simpa [hv0] using hdist.trans hle

lemma start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons h q =>
    have hnd := hp.support_nodup
    rw [Walk.support_cons] at hnd
    exact (List.nodup_cons.mp hnd).1

lemma not_adj_geodesic_far {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    {u : V} (hu : u ∈ P.support) {j : ℕ}
    (hj2 : 2 ≤ j) (hjr : j ≤ p.length)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1) :
    ¬ G.Adj u (p.getVert j) := by
  intro hadj
  obtain ⟨k, rfl, hk⟩ := (Walk.mem_support_iff_exists_getVert).mp hu
  have hd0u : G.dist v0 (P.getVert k) = k := dist_start_getVert P hP hk
  have hdw : G.dist (P.getVert k) w = P.length - k := dist_getVert_end P hP hk
  have hvu : G.dist v0 (p.getVert j) = j := dist_start_getVert p hlen hjr
  have hv2j : G.dist (p.getVert 2) (p.getVert j) = j - 2 :=
    dist_getVert p hlen hj2 hjr
  have hadj1 : G.dist (P.getVert k) (p.getVert j) = 1 := dist_eq_one_iff_adj.mpr hadj
  have hadj1' : G.dist (p.getVert j) (P.getVert k) = 1 := by
    rw [dist_comm, hadj1]
  have htri1 : j ≤ k + 1 := by
    have htri := hG.dist_triangle (u := v0) (v := P.getVert k) (w := p.getVert j)
    rw [hvu, hd0u, hadj1] at htri
    exact htri
  have hdwj : G.dist (p.getVert j) w ≤ 1 + (P.length - k) := by
    have htri := hG.dist_triangle (u := p.getVert j) (v := P.getVert k) (w := w)
    rw [hadj1', hdw] at htri
    exact htri
  have htri3 : G.dist (p.getVert 2) w ≤ j - 2 + G.dist (p.getVert j) w := by
    have htri := hG.dist_triangle (u := p.getVert 2) (v := p.getVert j) (w := w)
    rw [hv2j] at htri
    exact htri
  have hbound : G.dist (p.getVert 2) w ≤ P.length := by omega
  have hPlen : P.length ≤ p.length - 1 := by
    rw [hP]
    exact hw0
  omega

lemma adj_v1_of_P_is_first {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    {u : V} (hu : u ∈ P.support) (hne : u ≠ v0)
    (hadj : G.Adj (p.getVert 1) u)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1) :
    u = P.getVert 1 := by
  obtain ⟨k, rfl, hk⟩ := (Walk.mem_support_iff_exists_getVert).mp hu
  have hkpos : 0 < k := by
    by_contra h
    apply hne
    have : k = 0 := by omega
    simp [this]
  have hdw : G.dist (P.getVert k) w = P.length - k := dist_getVert_end P hP hk
  have hadj1 : G.dist (p.getVert 1) (P.getVert k) = 1 := dist_eq_one_iff_adj.mpr hadj
  have hv21 : G.dist (p.getVert 2) (p.getVert 1) = 1 := by
    rw [dist_comm]
    exact dist_getVert p hlen (by omega : (1 : ℕ) ≤ 2) hr
  have hv1w : G.dist (p.getVert 1) w ≤ 1 + (P.length - k) := by
    have htri := hG.dist_triangle (u := p.getVert 1) (v := P.getVert k) (w := w)
    rw [hadj1, hdw] at htri
    exact htri
  have hv2w : G.dist (p.getVert 2) w ≤ 1 + G.dist (p.getVert 1) w := by
    have htri := hG.dist_triangle (u := p.getVert 2) (v := p.getVert 1) (w := w)
    rw [hv21] at htri
    exact htri
  have hPlen : P.length ≤ p.length - 1 := by
    rw [hP]
    exact hw0
  have hkle : k ≤ 1 := by omega
  have : k = 1 := by omega
  simp [this]

lemma geodesic_not_on_P {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1)
    {j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ p.length) :
    p.getVert j ∉ P.support := by
  intro hmem
  obtain ⟨k, hk, hkle⟩ := (Walk.mem_support_iff_exists_getVert).mp hmem
  have hd0p : G.dist v0 (p.getVert j) = j := dist_start_getVert p hlen hjr
  have hd0P : G.dist v0 (P.getVert k) = k := dist_start_getVert P hP hkle
  have hkj : k = j := by
    rw [← hd0P, hk, hd0p]
  have hdw : G.dist (p.getVert j) w = P.length - k := by
    rw [← hk]
    exact dist_getVert_end P hP hkle
  have hPlen : P.length ≤ p.length - 1 := by
    rw [hP]
    exact hw0
  rcases le_or_gt j 1 with hj1 | hj2
  · have hj1' : j = 1 := by omega
    subst hj1'
    have hv21 : G.dist (p.getVert 2) (p.getVert 1) = 1 := by
      rw [dist_comm]
      exact dist_getVert p hlen (by omega : (1 : ℕ) ≤ 2) hr
    have htri : G.dist (p.getVert 2) w ≤ 1 + G.dist (p.getVert 1) w := by
      have h := hG.dist_triangle (u := p.getVert 2) (v := p.getVert 1) (w := w)
      rw [hv21] at h
      exact h
    omega
  · have hv2j : G.dist (p.getVert 2) (p.getVert j) = j - 2 :=
      dist_getVert p hlen (Nat.succ_le_of_lt hj2) hjr
    have htri : G.dist (p.getVert 2) w ≤ j - 2 + (P.length - k) := by
      have h := hG.dist_triangle (u := p.getVert 2) (v := p.getVert j) (w := w)
      rw [hv2j, hdw] at h
      exact h
    omega

lemma getVert_reverse_append {v0 vr w : V}
    (p : G.Walk v0 vr) (P : G.Walk v0 w) (i : ℕ) :
    (p.reverse.append P).getVert i =
      if i ≤ p.length then p.getVert (p.length - i) else P.getVert (i - p.length) := by
  rw [Walk.getVert_append', Walk.length_reverse]
  split_ifs with h
  · rw [Walk.getVert_reverse]
  · rfl

lemma nodup_reverse_append {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1) :
    (p.reverse.append P).support.Nodup := by
  have hp : p.IsPath := p.isPath_of_length_eq_dist hlen
  have hPp : P.IsPath := P.isPath_of_length_eq_dist hP
  rw [Walk.support_append, Walk.support_reverse]
  refine List.Nodup.append (List.nodup_reverse.mpr hp.support_nodup)
      hPp.support_nodup.tail ?_
  intro a ha hatail
  have haP : a ∈ P.support := List.mem_of_mem_tail hatail
  have hap : a ∈ p.support := by simpa using ha
  obtain ⟨j, rfl, hjr⟩ := (Walk.mem_support_iff_exists_getVert (p := p)).mp hap
  have hjpos : 1 ≤ j := by
    have : j ≠ 0 := by
      intro hj0
      have : p.getVert j = v0 := by simp [hj0]
      have : v0 ∈ P.support.tail := by simpa [this] using hatail
      exact start_not_mem_tail hPp this
    omega
  exact geodesic_not_on_P hG p hlen hr P hP hw hw0 hjpos hjr haP

lemma isInducedPath_reverse_append {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1)
    (hno : ∀ u ∈ P.support, u ≠ v0 → ¬ G.Adj (p.getVert 1) u) :
    isInducedPath G (p.reverse.append P).support := by
  refine isInducedPath_of_walk _ (nodup_reverse_append hG p hlen hr P hP hw hw0) ?_
  intro i j hij hjlen
  have hqlen : (p.reverse.append P).length = p.length + P.length := by simp
  have hi : i ≤ p.length + P.length := by omega
  have hjj : j ≤ p.length + P.length := by omega
  rw [getVert_reverse_append, getVert_reverse_append]
  split_ifs with hi' hj'
  · -- both on reverse geodesic; concatenated indices increase while geodesic indices decrease
    have hij' : p.length - j + 2 ≤ p.length - i := by omega
    exact fun hadj =>
      (not_adj_nonconsecutive_geodesic p hlen hij' (by omega : p.length - i ≤ p.length)) hadj.symm
  · have hjP : 0 < j - p.length := by omega
    by_cases hk : p.length - i = 0
    · have hge : 2 ≤ j - p.length := by omega
      have hnot := not_adj_nonconsecutive_geodesic P hP hge (by omega)
      have : p.getVert (p.length - i) = v0 := by simp [hk]
      simpa [this, Walk.getVert_zero] using hnot
    · have hki : 1 ≤ p.length - i := by omega
      have hki' : p.length - i ≤ p.length := by omega
      have hmem : P.getVert (j - p.length) ∈ P.support :=
        Walk.getVert_mem_support _ _
      by_cases h1 : p.length - i = 1
      · have : p.getVert (p.length - i) = p.getVert 1 := by simp [h1]
        have hne : P.getVert (j - p.length) ≠ v0 := by
          intro h0
          have : j - p.length = 0 :=
            getVert_injective_of_geodesic P hP (by omega) (Nat.zero_le _)
              (h0.trans (Walk.getVert_zero P).symm)
          omega
        exact fun h => (hno _ hmem hne (by simpa [this] using h))
      · have hj2 : 2 ≤ p.length - i := by omega
        exact fun h =>
          not_adj_geodesic_far hG p hlen P hP hmem hj2 hki' hw hw0 h.symm
  · -- i on P, j on reverse: impossible since i < j
    omega
  · -- both on P
    have hij' : (i - p.length) + 2 ≤ j - p.length := by omega
    exact not_adj_nonconsecutive_geodesic P hP hij' (by omega)

lemma reverse_take_end {v0 vr : V} (p : G.Walk v0 vr) (hp : 1 ≤ p.length) :
    p.reverse.getVert (p.length - 1) = p.getVert 1 := by
  rw [Walk.getVert_reverse]
  have : p.length - (p.length - 1) = 1 := by omega
  rw [this]

lemma r_sub_two_le_P_length {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (hw : p.length ≤ G.dist (p.getVert 2) w) :
    p.length - 2 ≤ G.dist v0 w := by
  have h20 : G.dist (p.getVert 2) v0 = 2 := by
    rw [dist_comm]
    exact dist_start_getVert p hlen (by omega)
  have htri := hG.dist_triangle (u := p.getVert 2) (v := v0) (w := w)
  omega

lemma extra_edge_imp_P_length {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1)
    (hp1 : 1 ≤ P.length)
    (hadj : G.Adj (p.getVert 1) (P.getVert 1)) :
    P.length = p.length - 1 := by
  have hv21 : G.dist (p.getVert 2) (p.getVert 1) = 1 := by
    rw [dist_comm]
    exact dist_getVert p hlen (by omega : (1 : ℕ) ≤ 2) hr
  have hadj1 : G.dist (p.getVert 1) (P.getVert 1) = 1 := dist_eq_one_iff_adj.mpr hadj
  have hdw : G.dist (P.getVert 1) w = P.length - 1 := dist_getVert_end P hP hp1
  have hv1w : G.dist (p.getVert 1) w ≤ 1 + (P.length - 1) := by
    have htri := hG.dist_triangle (u := p.getVert 1) (v := P.getVert 1) (w := w)
    rw [hadj1, hdw] at htri
    exact htri
  have hv2w : G.dist (p.getVert 2) w ≤ 1 + G.dist (p.getVert 1) w := by
    have htri := hG.dist_triangle (u := p.getVert 2) (v := p.getVert 1) (w := w)
    rw [hv21] at htri
    exact htri
  have hPlen : P.length ≤ p.length - 1 := by
    rw [hP]
    exact hw0
  omega

lemma getVert_chung_short {v0 vr w : V}
    (p : G.Walk v0 vr) (P : G.Walk v0 w)
    (hadj : G.Adj (p.getVert 1) (P.getVert 1))
    (hp : 1 ≤ p.length) (i : ℕ) :
    ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p hp)).concat
          hadj).append (P.drop 1)).getVert i =
      if i ≤ p.length - 1 then p.getVert (p.length - i)
      else P.getVert (i - (p.length - 1)) := by
  set pr := (p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p hp)
  have hprlen : pr.length = p.length - 1 := by
    simp [pr, Walk.take_length]
  have hclen : (pr.concat hadj).length = p.length := by
    simp [Walk.length_concat, hprlen]
    omega
  by_cases hi : i ≤ p.length - 1
  · have hiC : i ≤ (pr.concat hadj).length := by omega
    have hiP : i ≤ pr.length := by omega
    rw [Walk.getVert_append', if_pos hiC, Walk.concat, Walk.getVert_append', if_pos hiP]
    rw [Walk.getVert_copy, Walk.take_getVert, Walk.getVert_reverse]
    have hmin : (p.length - 1) ⊓ i = i := Nat.min_eq_right hi
    rw [hmin, if_pos hi]
  · by_cases hj : i ≤ p.length
    · have hi_eq : i = p.length := by omega
      have hiC : i ≤ (pr.concat hadj).length := by omega
      have hnot : ¬ i ≤ pr.length := by omega
      rw [Walk.getVert_append', if_pos hiC, Walk.concat, Walk.getVert_append', if_neg hnot]
      have hidx : i - pr.length = 1 := by omega
      have hidx' : i - (p.length - 1) = 1 := by omega
      rw [hidx]
      simp [hi, hidx']
    · have hnotC : ¬ i ≤ (pr.concat hadj).length := by omega
      rw [Walk.getVert_append', if_neg hnotC, Walk.drop_getVert, hclen]
      have : 1 + (i - p.length) = i - (p.length - 1) := by omega
      simp [hi, this]

lemma length_chung_short {v0 vr w : V}
    (p : G.Walk v0 vr) (P : G.Walk v0 w)
    (hadj : G.Adj (p.getVert 1) (P.getVert 1))
    (hp : 1 ≤ p.length) (hP : 1 ≤ P.length) :
    ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p hp)).concat
          hadj).append (P.drop 1)).length = p.length + P.length - 1 := by
  simp [Walk.length_append, Walk.length_concat, Walk.length_copy, Walk.take_length,
    Walk.drop_length, Walk.length_reverse]
  omega

lemma support_nodup_of_getVert_injective {u v : V} (q : G.Walk u v)
    (hinj : ∀ i j, i ≤ q.length → j ≤ q.length → q.getVert i = q.getVert j → i = j) :
    q.support.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro a b h
  apply Fin.ext
  have hi : a.val ≤ q.length := by have := a.isLt; have := q.length_support; omega
  have hj : b.val ≤ q.length := by have := b.isLt; have := q.length_support; omega
  exact hinj a.val b.val hi hj (by
    simpa [Walk.support_getElem_eq_getVert q a.isLt,
      Walk.support_getElem_eq_getVert q b.isLt] using h)

lemma nodup_chung_short {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1)
    (hpP : 1 ≤ P.length)
    (hadj : G.Adj (p.getVert 1) (P.getVert 1)) :
    ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p (by omega))).concat
          hadj).append (P.drop 1)).support.Nodup := by
  have hp1 : 1 ≤ p.length := by omega
  set q := ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p hp1)).concat
        hadj).append (P.drop 1))
  have hql : q.length = p.length + P.length - 1 :=
    length_chung_short p P hadj hp1 hpP
  refine support_nodup_of_getVert_injective q fun i j hi hj heq => ?_
  have hi' : i ≤ p.length + P.length - 1 := by omega
  have hj' : j ≤ p.length + P.length - 1 := by omega
  have hgi := getVert_chung_short p P hadj hp1 i
  have hgj := getVert_chung_short p P hadj hp1 j
  rw [hgi, hgj] at heq
  by_cases hiP : i ≤ p.length - 1
  · by_cases hjP : j ≤ p.length - 1
    · simp [hiP, hjP] at heq
      have hidx : p.length - i = p.length - j :=
        getVert_injective_of_geodesic p hlen (by omega) (by omega) heq
      omega
    · simp [hiP, hjP] at heq
      have hmem : p.getVert (p.length - i) ∈ P.support := by
        rw [heq]
        exact Walk.getVert_mem_support _ _
      have hki : 1 ≤ p.length - i := by omega
      exact (geodesic_not_on_P hG p hlen hr P hP hw hw0 hki (by omega) hmem).elim
  · by_cases hjP : j ≤ p.length - 1
    · simp [hiP, hjP] at heq
      have hmem : p.getVert (p.length - j) ∈ P.support := by
        rw [← heq]
        exact Walk.getVert_mem_support _ _
      have hkj : 1 ≤ p.length - j := by omega
      exact (geodesic_not_on_P hG p hlen hr P hP hw hw0 hkj (by omega) hmem).elim
    · simp [hiP, hjP] at heq
      have hij := getVert_injective_of_geodesic P hP (by omega) (by omega) heq
      omega

lemma isInducedPath_chung_short {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1)
    (hpP : 1 ≤ P.length)
    (hadj : G.Adj (p.getVert 1) (P.getVert 1)) :
    isInducedPath G
      ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p (by omega))).concat
            hadj).append (P.drop 1)).support := by
  have hp1 : 1 ≤ p.length := by omega
  refine isInducedPath_of_walk _
    (nodup_chung_short hG p hlen hr P hP hw hw0 hpP hadj) ?_
  intro i j hij hjlen
  have hql : ((((p.reverse.take (p.length - 1)).copy rfl (reverse_take_end p hp1)).concat
        hadj).append (P.drop 1)).length = p.length + P.length - 1 :=
    length_chung_short p P hadj hp1 hpP
  have hi : i ≤ p.length + P.length - 1 := by omega
  have hjle : j ≤ p.length + P.length - 1 := by omega
  rw [getVert_chung_short p P hadj hp1, getVert_chung_short p P hadj hp1]
  by_cases hi' : i ≤ p.length - 1
  · by_cases hj' : j ≤ p.length - 1
    · simp [hi', hj']
      have hij' : p.length - j + 2 ≤ p.length - i := by omega
      exact fun hadj' =>
        (not_adj_nonconsecutive_geodesic p hlen hij'
          (by omega : p.length - i ≤ p.length)) hadj'.symm
    · simp [hi', hj']
      have hki : 1 ≤ p.length - i := by omega
      have hki' : p.length - i ≤ p.length := by omega
      have hmem : P.getVert (j - (p.length - 1)) ∈ P.support :=
        Walk.getVert_mem_support _ _
      have hmj : 1 ≤ j - (p.length - 1) := by omega
      have hmj' : j - (p.length - 1) ≤ P.length := by omega
      by_cases h1 : p.length - i = 1
      · have hget : p.getVert (p.length - i) = p.getVert 1 := by simp [h1]
        have hne : P.getVert (j - (p.length - 1)) ≠ v0 := by
          intro h0
          have : j - (p.length - 1) = 0 :=
            getVert_injective_of_geodesic P hP (by omega) (Nat.zero_le _)
              (h0.trans (Walk.getVert_zero P).symm)
          omega
        intro hadj'
        have hfirst := adj_v1_of_P_is_first hG p hlen hr P hP hmem hne
          (by simpa [hget] using hadj') hw hw0
        have : j - (p.length - 1) = 1 :=
          getVert_injective_of_geodesic P hP hmj' (by omega) hfirst
        omega
      · have hj2 : 2 ≤ p.length - i := by omega
        exact fun h =>
          not_adj_geodesic_far hG p hlen P hP hmem hj2 hki' hw hw0 h.symm
  · by_cases hj' : j ≤ p.length - 1
    · omega
    · simp [hi', hj']
      have hij' : (i - (p.length - 1)) + 2 ≤ j - (p.length - 1) := by omega
      exact not_adj_nonconsecutive_geodesic P hP hij' (by omega)

lemma chung_exists_isInducedPath {v0 vr w : V} (hG : G.Connected)
    (p : G.Walk v0 vr) (hlen : p.length = G.dist v0 vr)
    (hr : 2 ≤ p.length)
    (P : G.Walk v0 w) (hP : P.length = G.dist v0 w)
    (hw : p.length ≤ G.dist (p.getVert 2) w)
    (hw0 : G.dist v0 w ≤ p.length - 1) :
    ∃ l : List V, isInducedPath G l ∧ 2 * p.length - 1 ≤ l.length := by
  classical
  by_cases hno : ∀ u ∈ P.support, u ≠ v0 → ¬ G.Adj (p.getVert 1) u
  · refine ⟨(p.reverse.append P).support,
      isInducedPath_reverse_append hG p hlen hr P hP hw hw0 hno, ?_⟩
    have hlen' : (p.reverse.append P).support.length = p.length + P.length + 1 := by
      simp [Walk.length_support, Walk.length_append, Walk.length_reverse]
    have hPge : p.length - 2 ≤ P.length := by
      have := r_sub_two_le_P_length hG p hlen hr hw
      omega
    omega
  · push Not at hno
    obtain ⟨u, hu, hne, hadj⟩ := hno
    have hu1 : u = P.getVert 1 :=
      adj_v1_of_P_is_first hG p hlen hr P hP hu hne hadj hw hw0
    have hadj' : G.Adj (p.getVert 1) (P.getVert 1) := by simpa [hu1] using hadj
    obtain ⟨k, hk, hkle⟩ := (Walk.mem_support_iff_exists_getVert).mp hu
    have hkpos : 0 < k := by
      by_contra h
      apply hne
      have : k = 0 := by omega
      rw [this] at hk
      simpa [Walk.getVert_zero] using hk.symm
    have hpP : 1 ≤ P.length := by omega
    have hPeq : P.length = p.length - 1 :=
      extra_edge_imp_P_length hG p hlen hr P hP hw hw0 hpP hadj'
    refine ⟨((((p.reverse.take (p.length - 1)).copy rfl
          (reverse_take_end p (by omega))).concat hadj').append (P.drop 1)).support,
      isInducedPath_chung_short hG p hlen hr P hP hw hw0 hpP hadj', ?_⟩
    have hql := length_chung_short p P hadj' (by omega : 1 ≤ p.length) hpP
    simp [Walk.length_support, hql]
    omega

end Dist

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_compl_singleton (vr : V) :
    Fintype.card ({vr}ᶜ : Set V) = Fintype.card V - 1 := by
  classical
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton,
    Nat.card_eq_fintype_card]

lemma path_ge_two_mul_radius_sub_one_of_card (n : ℕ) :
    ∀ (W : Type*) [Fintype W] [DecidableEq W] (G : SimpleGraph W)
      [DecidableRel G.Adj], Fintype.card W = n → G.Connected →
        2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ G _ hcard hG
    have : Nonempty W := hG.nonempty
    have hpath1 : 1 ≤ path G := one_le_path_of_nonempty G
    set r := G.radius.toNat with hrdef
    by_cases hr : r ≤ 1
    · have : 2 * r ≤ path G + 1 := by omega
      exact int_two_mul_sub_one_le this
    · have hr2 : 2 ≤ r := by omega
      have : Nontrivial W := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        have hz : G.radius = 0 := radius_eq_zero_iff.mpr ⟨hG.nonempty, hsub⟩
        have : r = 0 := by simp [hrdef, hz]
        omega
      obtain ⟨vr, hHconn⟩ :=
        hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
      let H := G.induce ({vr}ᶜ : Set W)
      have hcardH : Fintype.card ({vr}ᶜ : Set W) = n - 1 := by
        rw [card_compl_singleton, hcard]
      have hlt : Fintype.card ({vr}ᶜ : Set W) < n := by
        have : 1 < Fintype.card W := Fintype.one_lt_card
        omega
      by_cases hradH : r ≤ H.radius.toNat
      · have ihH := ih (Fintype.card ({vr}ᶜ : Set W)) hlt ({vr}ᶜ : Set W) H rfl hHconn
        have hle : path H ≤ path G := path_induce_le G ({vr}ᶜ)
        have hrle : (r : ℤ) ≤ H.radius.toNat := by exact_mod_cast hradH
        have hple : (path H : ℤ) ≤ path G := by exact_mod_cast hle
        omega
      · have hradH' : H.radius.toNat ≤ r - 1 := by
          have : ¬ r ≤ H.radius.toNat := hradH
          omega
        have : Nonempty ({vr}ᶜ : Set W) := hHconn.nonempty
        obtain ⟨v0, hv0⟩ := H.exists_eccent_eq_radius
        have hv0ne : (v0 : W) ≠ vr := v0.property
        have hle_all : ∀ x : W, x ≠ vr → G.dist (v0 : W) x ≤ r - 1 := by
          intro x hx
          have h1 := dist_v0_le_of_center (G := G) hHconn hv0 hx
          exact h1.trans hradH'
        obtain ⟨x, hxadj⟩ := hG.preconnected.exists_adj_of_nontrivial vr
        have hxne : x ≠ vr := hxadj.ne.symm
        have hdistx : G.dist (v0 : W) x ≤ r - 1 := hle_all x hxne
        have hle_vr : G.dist (v0 : W) vr ≤ r := by
          have htri := hG.dist_triangle (u := (v0 : W)) (v := x) (w := vr)
          have hx1 : G.dist x vr = 1 := dist_eq_one_iff_adj.mpr hxadj.symm
          omega
        obtain ⟨z, hz⟩ := exists_dist_eq_eccent hG (v0 : W)
        have hzr : r ≤ G.dist (v0 : W) z := by
          have := radius_le_eccent_toNat hG (v0 : W)
          omega
        have hzeq : z = vr := by
          by_contra hzne
          have := hle_all z hzne
          omega
        have hge_vr : r ≤ G.dist (v0 : W) vr := by simpa [hzeq] using hzr
        have hdist_vr : G.dist (v0 : W) vr = r := by omega
        obtain ⟨p, hlenp⟩ := hG.exists_walk_length_eq_dist (v0 : W) vr
        have hplen : p.length = r := by omega
        have hr2p : 2 ≤ p.length := by omega
        obtain ⟨w, hwecc⟩ := exists_dist_eq_eccent hG (p.getVert 2)
        have hw : p.length ≤ G.dist (p.getVert 2) w := by
          have := radius_le_eccent_toNat hG (p.getVert 2)
          omega
        have hwne : w ≠ vr := by
          intro hweq
          rw [hweq] at hw
          have hde : G.dist (p.getVert 2) vr = p.length - 2 :=
            dist_getVert_end p hlenp (by omega : 2 ≤ p.length)
          omega
        have hw0 : G.dist (v0 : W) w ≤ p.length - 1 := by
          have := hle_all w hwne
          omega
        obtain ⟨P, hP⟩ := hG.exists_walk_length_eq_dist (v0 : W) w
        obtain ⟨l, hl, hlenl⟩ :=
          chung_exists_isInducedPath hG p hlenp hr2p P hP hw hw0
        have hlepath := le_path_of_isInducedPath G hl
        have : 2 * r ≤ path G + 1 := by omega
        exact int_two_mul_sub_one_le this

theorem conjecture31 {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ) :=
  path_ge_two_mul_radius_sub_one_of_card (Fintype.card α) α G rfl h

example : ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj], G.Connected →
      2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ) :=
  conjecture31

#print axioms conjecture31

end Main

end WOWII31
