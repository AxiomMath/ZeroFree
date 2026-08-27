/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import ZeroFree.Abacus.Beads
public import ZeroFree.Meta.Attr

/-!
# The transpose of a bead set

`transpose N S` reflects `S` inside `range N` and complements; through the first-column hook
lengths it is the passage `λ ↦ λ'` from a partition to its conjugate. This is the vocabulary the
sign twist `χ^{λ'}(μ) = (-1)^{n-k} χ^λ(μ)` is stated in, and the transfer lemmas below — the
image of a rim hook, of its removal, and of its height — are what that identity is proved from.

## The width is an explicit argument, not inferred

At width `N` the transpose has `N - S.card` beads, so `transpose N S = S` forces
`N = 2 * S.card`. Self-conjugacy is exactly that fixed-point condition, and it is **not** a
property of `S` alone — the same `S` is self-conjugate at one width and not at another. Hence
`N` is carried rather than derived.

## The one fact everything here rests on

`σ y = N - 1 - y` is an involution of `range N`, and it is order-reversing, so it exchanges
"occupied below" with "unoccupied above". That single observation gives the rim-hook transfer
and the height reversal both.

## Main definitions

* `transpose`: reflect a bead set inside `range N`, then complement.

## Main results

* `mem_transpose_iff`: membership in the transpose of a bead set that fits the width.
* `isRimHook_transpose`: a length-`t` rim hook at `x` becomes one at `N - 1 - (x - t)`.
* `rimHookRemoval_transpose`: transposing commutes with rim-hook removal.
* `rimHookHeight_transpose_add`: the two rim-hook heights are complementary within `t - 1`.
* `beadSize_eq_zero_iff`: a bead set has size zero exactly when it is an initial segment.
* `transpose_range`: the transpose of an initial segment is an initial segment.
* `transpose_transpose`: the transpose is an involution at a fixed width.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- The transpose of a bead set at width `N`: reflect inside `range N`, then complement.

This is `λ ↦ λ'` read through the bead set: reflecting and complementing the first-column hook
lengths exchanges the rows and columns of the diagram. -/
@[zf_tag "def_transpose"]
def transpose (N : ℕ) (S : BeadSet) : BeadSet :=
  (range N) \ (S.image (fun s => N - 1 - s))

/-- Membership in the transpose, for a bead set that fits the width.

The `S ⊆ range N` hypothesis is what makes the reflection injective *on `S`*, so that
`N - 1 - s = y` can be inverted to `s = N - 1 - y`. Without it a bead at `s ≥ N` would reflect
to `0` by truncation and corrupt the answer. -/
theorem mem_transpose_iff {N : ℕ} {S : BeadSet} (hS : S ⊆ range N) {y : ℕ} :
    y ∈ transpose N S ↔ y < N ∧ N - 1 - y ∉ S := by
  classical
  simp only [transpose, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image,
    not_exists, not_and]
  constructor
  · rintro ⟨hyN, hno⟩
    refine ⟨hyN, fun hmem => ?_⟩
    have hlt : N - 1 - y < N := by omega
    exact hno _ hmem (by omega)
  · rintro ⟨hyN, hnot⟩
    refine ⟨hyN, ?_⟩
    intro s hsS hsy
    have hsN : s < N := Finset.mem_range.mp (hS hsS)
    exact hnot (by rwa [show N - 1 - y = s by omega])

/-- The reflection is an involution on the width. -/
theorem sub_sub_self_of_lt {N y : ℕ} (h : y < N) : N - 1 - (N - 1 - y) = y := by
  omega

/-- The transpose fits its own width. -/
theorem transpose_subset (N : ℕ) (S : BeadSet) : transpose N S ⊆ range N := by
  intro y hy
  exact (Finset.mem_sdiff.mp hy).1

/-- A rim hook of length `t` at `x` in `S` becomes one at `N - 1 - (x - t)` in the transpose.

The two membership conditions swap roles, which is the whole content: `x ∈ S` makes the *lower*
slot occupied here and unoccupied there, and `x - t ∉ S` does the reverse. -/
@[zf_tag "lem_transpose_rimhook"]
theorem isRimHook_transpose {N t x : ℕ} {S : BeadSet} (hS : S ⊆ range N)
    (ht : 1 ≤ t) (h : IsRimHook t S x) :
    IsRimHook t (transpose N S) (N - 1 - (x - t)) := by
  obtain ⟨hxS, htx, hx1⟩ := h
  have hxN : x < N := Finset.mem_range.mp (hS hxS)
  refine ⟨?_, ?_, ?_⟩
  · -- The vacated slot of `S` is occupied in the transpose.
    rw [mem_transpose_iff hS]
    refine ⟨by omega, ?_⟩
    rwa [show N - 1 - (N - 1 - (x - t)) = x - t by omega]
  · -- `x ≤ N - 1` leaves at least `t` room after reflecting.
    omega
  · -- The occupied slot of `S` is vacated in the transpose.
    rw [mem_transpose_iff hS]
    intro hcon
    exact hcon.2 (by rwa [show N - 1 - (N - 1 - (x - t) - t) = x by omega])

/-- Transposing commutes with removal: the move in the transpose is the transpose of the
move. -/
@[zf_tag "lem_transpose_removal"]
theorem rimHookRemoval_transpose {N t x : ℕ} {S : BeadSet} (hS : S ⊆ range N)
    (ht : 1 ≤ t) (h : IsRimHook t S x) :
    rimHookRemoval t (transpose N S) (N - 1 - (x - t))
      = transpose N (rimHookRemoval t S x) := by
  classical
  obtain ⟨hxS, htx, hx1⟩ := h
  have hxN : x < N := Finset.mem_range.mp (hS hxS)
  have hsub : (insert (x - t) (S.erase x) : BeadSet) ⊆ range N := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact Finset.mem_range.mpr (by omega)
    · exact hS (Finset.mem_of_mem_erase hy')
  ext y
  simp only [rimHookRemoval, Finset.mem_insert, Finset.mem_erase,
    mem_transpose_iff hS, mem_transpose_iff hsub]
  constructor
  · rintro (rfl | ⟨hyX, hyN, hyS⟩)
    · -- The arriving bead is the reflection of `x`, and `x` is what the move drops.
      refine ⟨by omega, ?_⟩
      rintro (heq | ⟨hne, -⟩)
      · omega
      · exact hne (by omega)
    · refine ⟨hyN, ?_⟩
      rintro (heq | ⟨-, hmem⟩)
      · exact hyX (by omega)
      · exact hyS hmem
  · rintro ⟨hyN, hno⟩
    by_cases hcase : N - 1 - y = x
    · -- `y` is the reflection of `x`: the arriving slot.
      exact Or.inl (by omega)
    · refine Or.inr ⟨fun hEq => hno (Or.inl (by omega)), hyN, fun hmem =>
        hno (Or.inr ⟨hcase, hmem⟩)⟩

/-! ### The height reversal

The part that carries the sign. Stated additively, as `h' + h = t - 1`, so that no truncated
subtraction appears.

The argument is a count of the `t - 1` slots strictly between the vacated and the occupied
position. Reflection is a bijection of that interval onto the corresponding interval of the
transpose, and it exchanges occupied with unoccupied — so the two heights are complementary
within `t - 1`. -/

/-- The open interval between a rim hook's endpoints has `t - 1` slots. -/
theorem card_Ioo_rimHook {t x : ℕ} (htx : t ≤ x) :
    (Finset.Ioo (x - t) x).card = t - 1 := by
  rw [Nat.card_Ioo]
  omega

/-- The height, as a count over the interval rather than over the bead set: the two filters
describe the same finset. -/
theorem rimHookHeight_eq_filter_Ioo {t x : ℕ} {S : BeadSet} :
    rimHookHeight t S x = ((Finset.Ioo (x - t) x).filter (fun y => y ∈ S)).card := by
  classical
  have hset : S.filter (fun y => x - t < y ∧ y < x)
      = (Finset.Ioo (x - t) x).filter (fun y => y ∈ S) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    tauto
  rw [rimHookHeight, hset]

/-- Reflection exchanges occupied with unoccupied on the interval, so the height of a rim hook
and the height of its transpose are complementary within `t - 1`. -/
@[zf_tag "lem_transpose_height"]
theorem rimHookHeight_transpose_add {N t x : ℕ} {S : BeadSet} (hS : S ⊆ range N)
    (ht : 1 ≤ t) (h : IsRimHook t S x) :
    rimHookHeight t (transpose N S) (N - 1 - (x - t)) + rimHookHeight t S x
      = t - 1 := by
  classical
  obtain ⟨hxS, htx, hx1⟩ := h
  have hxN : x < N := Finset.mem_range.mp (hS hxS)
  -- The transposed height counts the unoccupied slots of the same interval.
  have himg : (transpose N S).filter
        (fun y => N - 1 - (x - t) - t < y ∧ y < N - 1 - (x - t))
      = ((Finset.Ioo (x - t) x).filter (fun z => z ∉ S)).image (fun z => N - 1 - z) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ioo,
      mem_transpose_iff hS]
    constructor
    · rintro ⟨⟨hyN, hyS⟩, h1, h2⟩
      exact ⟨N - 1 - y, ⟨⟨by omega, by omega⟩, hyS⟩, by omega⟩
    · rintro ⟨z, ⟨⟨h1, h2⟩, hzS⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, by omega, by omega⟩
      rwa [show N - 1 - (N - 1 - z) = z by omega]
  have hinj : Set.InjOn (fun z => N - 1 - z)
      ((Finset.Ioo (x - t) x).filter (fun z => z ∉ S)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioo] at ha hb
    replace hab : N - 1 - a = N - 1 - b := hab
    omega
  have hT : rimHookHeight t (transpose N S) (N - 1 - (x - t))
      = ((Finset.Ioo (x - t) x).filter (fun z => z ∉ S)).card := by
    rw [rimHookHeight, himg, Finset.card_image_of_injOn hinj]
  rw [hT, rimHookHeight_eq_filter_Ioo, ← card_Ioo_rimHook (t := t) htx, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-! ### The empty-diagram base case

`chi` on the empty list returns `1` or `0` according as the size vanishes, so the induction for
the sign twist needs the transpose to preserve *having size zero*. And `beadSize S = 0` says
exactly that `S` is an initial segment: `exists_descentChain_to_range` produces a chain of
length `beadSize S` ending at `range S.card`, so a zero-length chain forces
`S = range S.card`. -/

/-- A length-zero descent chain is trivial. -/
theorem DescentChain.eq_of_zero {P Q : Finset ℕ} (h : DescentChain 0 P Q) :
    P = Q := by
  cases h with
  | refl => rfl

/-- **A bead set has size zero exactly when it is an initial segment.** -/
theorem beadSize_eq_zero_iff {S : BeadSet} : beadSize S = 0 ↔ S = range S.card := by
  constructor
  · intro h
    have hch := exists_descentChain_to_range S
    rw [beadSize] at h
    rw [h] at hch
    exact DescentChain.eq_of_zero hch
  · intro h
    have hsum : (∑ x ∈ S, x) = ∑ j ∈ range S.card, j := by conv_lhs => rw [h]
    rw [beadSize, hsum, Nat.sub_self]

/-- Reflecting an initial segment gives an initial segment. -/
theorem transpose_range {m N : ℕ} (h : m ≤ N) :
    transpose N (range m) = range (N - m) := by
  classical
  ext y
  rw [mem_transpose_iff (fun z hz => mem_range.mpr
    (lt_of_lt_of_le (mem_range.mp hz) h))]
  simp only [Finset.mem_range]
  omega

/-- The transpose is an involution at a fixed width. -/
theorem transpose_transpose {N : ℕ} {S : BeadSet} (hS : S ⊆ range N) :
    transpose N (transpose N S) = S := by
  classical
  ext y
  rw [mem_transpose_iff (transpose_subset N S), mem_transpose_iff hS]
  constructor
  · rintro ⟨hyN, hno⟩
    by_contra hyS
    exact hno ⟨by omega, by rwa [show N - 1 - (N - 1 - y) = y by omega]⟩
  · intro hyS
    have hyN : y < N := mem_range.mp (hS hyS)
    refine ⟨hyN, ?_⟩
    rintro ⟨-, hc⟩
    exact hc (by rwa [show N - 1 - (N - 1 - y) = y by omega])

end ZeroFree
