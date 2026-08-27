/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import ZeroFree.Abacus.Beads
public import ZeroFree.Arithmetic.Basic
public import ZeroFree.Meta.Attr

/-!
# The staircase bead set

The staircase partition `(u, u-1, …, 1)` has as its bead set the odd numbers below `2u`. It is a
`2`-core, and its size is the triangular number `tri u`, so every triangular number is the size of
a `2`-core.

## Main definitions

* `ZeroFree.staircase`: the bead set of the staircase partition `(u, u-1, …, 1)`.

## Main results

* `ZeroFree.beadSize_staircase`: the staircase has size `tri u`.
* `ZeroFree.staircase_isTCore_two`: the staircase is a `2`-core.
* `ZeroFree.exists_tcore_two_of_tri`: every triangular number is the size of a `2`-core.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- The bead set of the staircase `(u, u-1, …, 1)`: the odd numbers below `2u`. -/
def staircase (u : ℕ) : BeadSet := (range u).image (fun j => 2 * j + 1)

theorem card_staircase (u : ℕ) : (staircase u).card = u := by
  rw [staircase, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_range]

theorem mem_staircase {u x : ℕ} : x ∈ staircase u ↔ ∃ j < u, x = 2 * j + 1 := by
  simp only [staircase, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

/-- Gauss's sum in a truncation-free form: `2·(0+1+⋯+(u-1)) + u = u²`, avoiding the `ℕ`
subtraction of `Finset.sum_range_id_mul_two`. -/
theorem two_mul_sum_range_add (u : ℕ) : 2 * (∑ j ∈ range u, j) + u = u * u := by
  induction u with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_range_succ]
    have hexp : (v + 1) * (v + 1) = v * v + 2 * v + 1 := by ring
    omega

/-- The staircase has size the triangular number `tri u`. -/
theorem beadSize_staircase (u : ℕ) : beadSize (staircase u) = tri u := by
  have hsum : ∑ x ∈ staircase u, x = 2 * (∑ j ∈ range u, j) + u := by
    rw [staircase, Finset.sum_image (fun a _ b _ h => by omega)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range]
    ring
  have hsz := size_beta (staircase u)
  rw [card_staircase] at hsz
  have htri : 2 * tri u = u * (u + 1) := two_mul_tri u
  have hgauss := two_mul_sum_range_add u
  obtain ⟨w, hw⟩ : ∃ w, w = ∑ j ∈ range u, j := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = u * u := ⟨_, rfl⟩
  have htri' : 2 * tri u = q + u := by rw [hq, htri]; ring
  rw [← hw] at hsum hsz hgauss
  rw [← hq] at hgauss
  omega

/-- The staircase is a `2`-core: every odd bead above `1` has its predecessor two
places down already occupied. -/
theorem staircase_isTCore_two (u : ℕ) : IsTCore 2 (staircase u) := by
  intro x ⟨hxS, h2x, hx2⟩
  obtain ⟨j, hj, rfl⟩ := mem_staircase.mp hxS
  exact hx2 (mem_staircase.mpr ⟨j - 1, by omega, by omega⟩)

/-- Every triangular number `tri u` is the size of a `2`-core, witnessed by the staircase
`(u, u-1, …, 1)` on `u` beads. -/
@[zf_tag "lem_2core"]
theorem exists_tcore_two_of_tri (u : ℕ) :
    ∃ S : BeadSet, S.card = u ∧ beadSize S = tri u ∧ IsTCore 2 S :=
  ⟨staircase u, card_staircase u, beadSize_staircase u, staircase_isTCore_two u⟩

end ZeroFree
