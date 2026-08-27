/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import ZeroFree.Abacus.Transpose
public import ZeroFree.Meta.Attr

/-!
# Existence of a self-conjugate partition

For every `n ≥ 3` there is a self-conjugate partition of `n`: a hook for odd `n` and a near-hook
for even `n`, both exhibited directly as bead sets.

## Main results

* `ZeroFree.selfconj_odd`: the hook `(i+2, 1^{i+1})` is self-conjugate of size `2i+3`.
* `ZeroFree.selfconj_even`: the near-hook `(j+2, 2, 1^j)` is self-conjugate of size `2j+4`.
* `ZeroFree.exists_selfconj`: every `n ≥ 3` is the size of a self-conjugate partition.

## Self-conjugacy is a fixed point, and the width is what makes it one

At width `N` the transpose of an `m`-bead set has `N - m` beads, so `transpose N S = S` forces
`N = 2 * S.card`. Self-conjugacy is therefore not a property of `S` alone — the same `S` is
self-conjugate at one width and not at another — which is why `transpose` carries the width
explicitly. The statements below pin it as `2 * S.card`, so no separate hypothesis is needed.

## The two constructions

Read through `β` (with `β_k(λ) = {λ_i + k - i}`) the hook and the near-hook become bead sets
directly, with no partition ever constructed:

| `n` | `λ` | bead set | width |
| --- | --- | --- | --- |
| `2i+3` | `(i+2, 1^{i+1})` | `{2i+3} ∪ [1, i+1]` | `2i+4` |
| `2j+4` | `(j+2, 2, 1^j)` | `{2j+3, j+2} ∪ [1, j]` | `2j+4` |

Both are parametrised so that **no truncated subtraction appears**: writing the even case as
`n = 2j+4` rather than `n = 2m` with `m ≥ 2` keeps `m - 2` out of the statement entirely, and
`omega` then handles the membership arithmetic directly.

Sizes are computed through `size_beta`, never in closed form. In the odd case `∑ (range (i+2))`
and `∑ (Icc 1 (i+1))` are *equal* — the first is the second with a harmless `0` adjoined — so they
cancel and the size falls out as `2i+3` with no Gauss formula. The even case cancels the same way
against a shifted interval.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- `range (k+1)` is `Icc 1 k` with `0` adjoined, so the two have equal sums. -/
theorem sum_range_succ_eq_sum_Icc (k : ℕ) :
    ∑ j ∈ range (k + 1), j = ∑ j ∈ Icc 1 k, j := by
  classical
  have h : range (k + 1) = insert 0 (Icc 1 k) := by
    ext y
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), Nat.zero_add]

/-- `{2i+3} ∪ [1, i+1]`, the bead form of the hook `(i+2, 1^{i+1})`, is self-conjugate of size
`2i+3` at width `2i+4`. -/
theorem selfconj_odd (i : ℕ) :
    ∃ S : BeadSet, S ⊆ range (2 * S.card) ∧ beadSize S = 2 * i + 3 ∧
      transpose (2 * S.card) S = S := by
  classical
  have hnot : (2 * i + 3) ∉ Icc 1 (i + 1) := by simp only [Finset.mem_Icc]; omega
  have hcard : (insert (2 * i + 3) (Icc 1 (i + 1)) : BeadSet).card = i + 2 := by
    rw [Finset.card_insert_of_notMem hnot, Nat.card_Icc]
    omega
  have hsub : (insert (2 * i + 3) (Icc 1 (i + 1)) : BeadSet) ⊆ range (2 * (i + 2)) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_Icc] at hy
    exact mem_range.mpr (by omega)
  refine ⟨insert (2 * i + 3) (Icc 1 (i + 1)), by rw [hcard]; exact hsub, ?_, ?_⟩
  · have hsum := size_beta (insert (2 * i + 3) (Icc 1 (i + 1)) : BeadSet)
    rw [hcard, Finset.sum_insert hnot, sum_range_succ_eq_sum_Icc] at hsum
    omega
  · rw [hcard]
    ext y
    rw [mem_transpose_iff hsub]
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

/-- `{2j+3, j+2} ∪ [1, j]`, the bead form of the near-hook `(j+2, 2, 1^j)`, is self-conjugate of
size `2j+4` at width `2j+4`.

Parametrised by `j = m - 2` so that no truncated subtraction reaches the statement; at `j = 0` the
interval is empty and the set is `{2, 3}`. -/
theorem selfconj_even (j : ℕ) :
    ∃ S : BeadSet, S ⊆ range (2 * S.card) ∧ beadSize S = 2 * j + 4 ∧
      transpose (2 * S.card) S = S := by
  classical
  have hnot2 : (j + 2) ∉ Icc 1 j := by simp only [Finset.mem_Icc]; omega
  have hnot1 : (2 * j + 3) ∉ insert (j + 2) (Icc 1 j) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hcard : (insert (2 * j + 3) (insert (j + 2) (Icc 1 j)) : BeadSet).card = j + 2 := by
    rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
      Nat.card_Icc]
    omega
  have hsub : (insert (2 * j + 3) (insert (j + 2) (Icc 1 j)) : BeadSet)
      ⊆ range (2 * (j + 2)) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_Icc] at hy
    exact mem_range.mpr (by omega)
  refine ⟨insert (2 * j + 3) (insert (j + 2) (Icc 1 j)), by rw [hcard]; exact hsub,
    ?_, ?_⟩
  · have hsum := size_beta (insert (2 * j + 3) (insert (j + 2) (Icc 1 j)) : BeadSet)
    rw [hcard, Finset.sum_insert hnot1, Finset.sum_insert hnot2] at hsum
    rw [sum_range_succ_eq_sum_Icc] at hsum
    have hshift : ∑ x ∈ Icc 1 (j + 1), x = (j + 1) + ∑ x ∈ Icc 1 j, x := by
      rw [show Icc 1 (j + 1) = insert (j + 1) (Icc 1 j) by
        ext y; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    omega
  · rw [hcard]
    ext y
    rw [mem_transpose_iff hsub]
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

/-- Every `n ≥ 3` is the size of a self-conjugate partition: `n ≥ 3` splits as `2i+3` or `2j+4`,
which is the odd/even split of the hook and near-hook constructions. -/
@[zf_tag "lem_selfconj"]
theorem exists_selfconj {n : ℕ} (hn : 3 ≤ n) :
    ∃ S : BeadSet, S ⊆ range (2 * S.card) ∧ beadSize S = n ∧
      transpose (2 * S.card) S = S := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨j, hj⟩ : ∃ j, n = 2 * j + 4 := by
      obtain ⟨r, hr⟩ := he; exact ⟨r - 2, by omega⟩
    rw [hj]; exact selfconj_even j
  · obtain ⟨i, hi⟩ : ∃ i, n = 2 * i + 3 := by
      obtain ⟨r, hr⟩ := ho; exact ⟨r - 1, by omega⟩
    rw [hi]; exact selfconj_odd i

end ZeroFree
