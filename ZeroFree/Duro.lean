/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Cutoff
public import ZeroFree.OddClass

/-!
# Duro's reduction

A zero-free column forces every part of `μ` into `{1, 2, 3}` and forces an even number of parts
equal to `2`. Both halves are contradictions: a part `t ≥ 4` gives a vanishing character value by
`exists_chi_eq_zero_of_four_le_part`, and an odd number of parts equal to `2` gives one by
`exists_chi_eq_zero_of_odd_twos`.

The second witness is a self-conjugate bead set, whose bead count need not be `n`, while
`ZeroFreeColumn` quantifies over bead sets of card exactly `n`. Renormalizing it is padding —
`padBeads` upwards, `unpadBeads` downwards — under which `chi` is invariant: for `t ≥ 1` the rim
hooks of `{0} ∪ (S + 1)` are precisely the rim hooks of `S` shifted up by one. The new bead at
slot `0` is never a rim hook, and it blocks nothing, since a bead landing in slot `0` after its
move would have had `x = t`, which is not a rim hook of the padded set because slot `0` is
occupied. The height is a count of beads strictly between two slots, so it is shift-invariant, and
removal commutes with padding, so the two sums of `chi_cons` match term by term.

## Main definitions

* `unpadBeads`: the inverse of `padBeads` on bead sets occupying slot `0`.

## Main results

* `chi_padBeads`: `chi` is invariant under adding a zero part to the partition.
* `exists_card_eq_of_chi_eq_zero`: a vanishing witness of size `n` can be moved onto a bead set
  with exactly `n` beads.
* `parts_mem_and_count_two_even`: Duro's reduction.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-! ### Rim hooks of a padded bead set -/

/-- The padded bead set occupies slot `0`, so no rim hook of it can move a bead *into* slot `0`:
the vacated slot is strictly positive. -/
theorem lt_of_isRimHook_padBeads {t x : ℕ} {S : BeadSet}
    (h : IsRimHook t (padBeads S) x) : t < x := by
  rcases Nat.lt_or_ge t x with h1 | h1
  · exact h1
  · exact absurd (mem_padBeads.mpr (Or.inl (by omega))) h.2.2

/-- Padding shifts the erased slot up by one. -/
theorem erase_padBeads_succ (S : BeadSet) (y : ℕ) :
    (padBeads S).erase (y + 1) = padBeads (S.erase y) := by
  classical
  rw [padBeads, padBeads, Finset.erase_insert_of_ne (by omega),
    ← Finset.image_erase (add_left_injective 1) S y]

/-- Rim-hook removal commutes with padding. -/
theorem rimHookRemoval_padBeads {t y : ℕ} (h : t ≤ y) (S : BeadSet) :
    rimHookRemoval t (padBeads S) (y + 1) = padBeads (rimHookRemoval t S y) := by
  classical
  have hy : y + 1 - t = y - t + 1 := by omega
  rw [rimHookRemoval, hy, erase_padBeads_succ, rimHookRemoval]
  simp only [padBeads, Finset.image_insert]
  exact Finset.insert_comm _ _ _

/-- The height of a rim hook counts beads strictly between two slots, so it is invariant under the
shift that padding performs. -/
theorem rimHookHeight_padBeads {t y : ℕ} (h : t ≤ y) (S : BeadSet) :
    rimHookHeight t (padBeads S) (y + 1) = rimHookHeight t S y := by
  classical
  have hset : (padBeads S).filter (fun z => y + 1 - t < z ∧ z < y + 1)
      = (S.filter (fun u => y - t < u ∧ u < y)).image (· + 1) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image, mem_padBeads]
    constructor
    · rintro ⟨rfl | ⟨u, hu, rfl⟩, h1, h2⟩
      · exact absurd h1 (by omega)
      · exact ⟨u, ⟨hu, by omega⟩, rfl⟩
    · rintro ⟨u, ⟨hu, h1, h2⟩, rfl⟩
      exact ⟨Or.inr ⟨u, hu, rfl⟩, by omega⟩
  rw [rimHookHeight, rimHookHeight, hset,
    Finset.card_image_of_injective _ (add_left_injective 1)]

/-! ### `chi` is invariant under padding -/

/-- Adding a zero part to the partition — `S ↦ {0} ∪ (S + 1)` — leaves the character value
unchanged. -/
theorem chi_padBeads (S : BeadSet) (w : List ℕ) : chi (padBeads S) w = chi S w := by
  classical
  induction w generalizing S with
  | nil => rw [chi_nil, chi_nil, beadSize_padBeads]
  | cons t v ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [chi_cons_zero, chi_cons_zero]
    rw [chi_cons, chi_cons]
    refine Finset.sum_nbij' (i := fun x => x - 1) (j := fun x => x + 1) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hrh := mem_chi_filter.mp hx
      have hlt := lt_of_isRimHook_padBeads hrh
      obtain ⟨hxS, htx, hnot⟩ := hrh
      obtain rfl | ⟨u, hu, rfl⟩ := mem_padBeads.mp hxS
      · omega
      refine mem_chi_filter.mpr ⟨by simpa using hu, by omega, fun hmem => hnot ?_⟩
      exact mem_padBeads.mpr (Or.inr ⟨u + 1 - 1 - t, hmem, by omega⟩)
    · intro u hu
      obtain ⟨huS, htu, hnot⟩ := mem_chi_filter.mp hu
      refine mem_chi_filter.mpr ⟨mem_padBeads.mpr (Or.inr ⟨u, huS, rfl⟩), by omega, ?_⟩
      intro hmem
      obtain h0 | ⟨z, hz, hz1⟩ := mem_padBeads.mp hmem
      · omega
      · exact hnot (by have : z = u - t := by omega
                       exact this ▸ hz)
    · intro x hx
      have hlt := lt_of_isRimHook_padBeads (mem_chi_filter.mp hx)
      omega
    · intro u _
      omega
    · intro x hx
      have hrh := mem_chi_filter.mp hx
      have hlt := lt_of_isRimHook_padBeads hrh
      obtain ⟨u, rfl⟩ : ∃ u, x = u + 1 := ⟨x - 1, by omega⟩
      have hu : t ≤ u := by omega
      simp only [Nat.add_sub_cancel]
      rw [rimHookHeight_padBeads hu S, rimHookRemoval_padBeads hu S, ih]

/-- Padding invariance, iterated. -/
theorem chi_padBeads_iterate (S : BeadSet) (w : List ℕ) (k : ℕ) :
    chi (padBeads^[k] S) w = chi S w := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', chi_padBeads, ih]

/-! ### Removing a zero part -/

/-- The inverse of `padBeads` on bead sets occupying slot `0`: every bead moves down one slot and
the bead in slot `0` is discarded. -/
def unpadBeads (S : BeadSet) : BeadSet := (S.erase 0).image (· - 1)

/-- A bead set occupying slot `0` is a padding. -/
theorem padBeads_unpadBeads {S : BeadSet} (h : 0 ∈ S) : padBeads (unpadBeads S) = S := by
  classical
  ext x
  simp only [mem_padBeads, unpadBeads, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨y, ⟨u, ⟨hu0, huS⟩, rfl⟩, rfl⟩)
    · exact h
    · have : u - 1 + 1 = u := by omega
      exact this ▸ huS
  · intro hx
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · exact Or.inl rfl
    · exact Or.inr ⟨x - 1, ⟨x, ⟨by omega, hx⟩, rfl⟩, by omega⟩

/-- A bead set that misses slot `0` has at most as many beads as its size: each of its `m` beads is
at least `1`, so `size_beta` applied to `S - 1` leaves `m` to spare. -/
theorem card_le_beadSize_of_zero_notMem {S : BeadSet} (h : 0 ∉ S) :
    S.card ≤ beadSize S := by
  classical
  have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => Nat.one_le_iff_ne_zero.mpr fun h0 => h (h0 ▸ hx)
  have hinj : ∀ x ∈ S, ∀ y ∈ S, x - 1 = y - 1 → x = y := by
    intro x hx y hy hxy
    have := hpos x hx
    have := hpos y hy
    omega
  have hcard : (S.image (· - 1)).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hsum : (∑ u ∈ S.image (· - 1), u) + S.card = ∑ x ∈ S, x := by
    rw [Finset.sum_image hinj]
    have : ∀ x ∈ S, x = x - 1 + 1 := fun x hx => by have := hpos x hx; omega
    calc (∑ x ∈ S, (x - 1)) + S.card
        = ∑ x ∈ S, (x - 1 + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ x ∈ S, x := (Finset.sum_congr rfl this).symm
  have hlow := sum_range_card_le_sum (S.image (· - 1))
  rw [hcard] at hlow
  have := size_beta S
  omega

/-! ### The card-`n` normalization of a vanishing witness -/

/-- Given a bead set of size `n` on which `chi` vanishes, padding up or down produces one with
exactly `n` beads, the normalization `ZeroFreeColumn` quantifies over. -/
theorem exists_card_eq_of_chi_eq_zero {n : ℕ} (w : List ℕ) :
    ∀ m : ℕ, ∀ S : BeadSet, S.card = m → beadSize S = n → chi S w = 0 →
      ∃ T : BeadSet, T.card = n ∧ beadSize T = n ∧ chi T w = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hcard hsize hzero
    rcases Nat.lt_or_ge n m with hlt | hle
    · have h0 : 0 ∈ S := by
        by_contra h
        have := card_le_beadSize_of_zero_notMem h
        omega
      have hpad := padBeads_unpadBeads h0
      have hcardu : (unpadBeads S).card + 1 = m := by
        rw [← card_padBeads, hpad, hcard]
      refine ih (unpadBeads S).card (by omega) (unpadBeads S) rfl ?_ ?_
      · have := beadSize_padBeads (unpadBeads S)
        rw [hpad] at this
        omega
      · have := chi_padBeads (unpadBeads S) w
        rw [hpad] at this
        rw [← this]
        exact hzero
    · refine ⟨padBeads^[n - m] S, ?_, ?_, ?_⟩
      · rw [card_padBeads_iterate, hcard]; omega
      · rw [beadSize_padBeads_iterate]; exact hsize
      · rw [chi_padBeads_iterate]; exact hzero

/-! ### Duro's reduction -/

/-- *Duro's reduction.* If `n ≥ 3` and `μ ⊢ n` has a zero-free column, then every part of `μ` lies
in `{1, 2, 3}` and the number of parts equal to `2` is even. -/
@[zf_tag "prop_duro"]
theorem parts_mem_and_count_two_even (L : LiteratureInputs) {n : ℕ} (hn : 3 ≤ n)
    (μ : Nat.Partition n) (hμ : ZeroFreeColumn n μ) :
    (∀ t ∈ μ.parts, t = 1 ∨ t = 2 ∨ t = 3) ∧ μ.parts.count 2 % 2 = 0 := by
  classical
  have h123 : ∀ t ∈ μ.parts, t = 1 ∨ t = 2 ∨ t = 3 := by
    intro t ht
    have hpos : 0 < t := μ.parts_pos ht
    rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ 4 ≤ t) with h | h | h | h4
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    obtain ⟨S, hcard, hsize, hzero⟩ :=
      exists_chi_eq_zero_of_four_le_part L h4 (by omega : 1 ≤ n) μ ht
    exact absurd hzero (hμ S hcard hsize)
  refine ⟨h123, ?_⟩
  by_contra hodd
  have hsum : μ.parts.toList.sum = n := by rw [Multiset.sum_toList]; exact μ.parts_sum
  have hcount : μ.parts.toList.count 2 = μ.parts.count 2 := by
    rw [← Multiset.coe_count, Multiset.coe_toList]
  have hw : ∀ t ∈ μ.parts.toList, t = 1 ∨ t = 2 ∨ t = 3 :=
    fun t ht => h123 t (Multiset.mem_toList.mp ht)
  obtain ⟨S, hsize, hzero⟩ :=
    exists_chi_eq_zero_of_odd_twos hw (by rw [hcount]; omega) (by rw [hsum]; omega)
  rw [hsum] at hsize
  obtain ⟨T, hTcard, hTsize, hTzero⟩ :=
    exists_card_eq_of_chi_eq_zero μ.parts.toList S.card S rfl hsize hzero
  exact hμ T hTcard hTsize hTzero

end ZeroFree
