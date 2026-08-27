/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import ZeroFree.Meta.Attr

/-!
# Descents of a finite set of naturals

A *descent* of a finite set `P` of naturals replaces one element `x` by `x - 1`, and is
permitted only when `x ≠ 0` and the target slot `x - 1` is unoccupied. In the abacus picture it
is one bead moving one place left on its runner.

The result proved here is that the longest chain of descents starting from `P` has length
```
∑ x ∈ P, x  -  ∑ j ∈ range P.card, j
```
and that a longest chain ends at `range P.card`, the unique descent-free configuration of that
cardinality. Nothing here mentions partitions: this is the combinatorial core of the abacus
argument, proved against `Finset ℕ` alone.

## Main definitions

* `IsDescent`: `Q` is obtained from `P` by moving a single element down by one.
* `DescentChain`: `Q` is reachable from `P` by exactly `n` descents.

## Main results

* `eq_range_of_no_descent`: a descent-free finite set of naturals is `range` of its own card.
* `sum_range_card_le_sum`: `∑ j ∈ range P.card, j ≤ ∑ x ∈ P, x`.
* `DescentChain.sum_add`: the chain length is exactly the drop in the sum.
* `DescentChain.length_le`: no chain from `P` is longer than `∑ P - ∑ range P.card`.
* `exists_descentChain_to_range`: that length is attained, by a chain ending at `range P.card`.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- `IsDescent P Q`: `Q` is obtained from `P` by moving a single element `x` down to `x - 1`,
which is permitted exactly when `x ≠ 0` and `x - 1` is not already occupied.

In the abacus picture it is one bead moving one place left on its runner, and it is exactly the
removal of a rim hook of length `1`. -/
@[zf_tag "def_descent"]
def IsDescent (P Q : Finset ℕ) : Prop :=
  ∃ x ∈ P, x ≠ 0 ∧ x - 1 ∉ P ∧ Q = insert (x - 1) (P.erase x)

variable {P Q R : Finset ℕ} {n : ℕ}

/-- A descent preserves the number of elements: one leaves, one arrives. -/
theorem IsDescent.card_eq (h : IsDescent P Q) : Q.card = P.card := by
  obtain ⟨x, hxP, _, hx1, rfl⟩ := h
  have hne : x - 1 ∉ P.erase x := fun hmem => hx1 (mem_of_mem_erase hmem)
  have hpos : 1 ≤ P.card := card_pos.mpr ⟨x, hxP⟩
  rw [card_insert_of_notMem hne, card_erase_of_mem hxP]
  omega

/-- A descent decreases the sum by exactly one, stated additively so that no truncated
subtraction enters the proofs that chain descents together. -/
theorem IsDescent.sum_succ (h : IsDescent P Q) : (∑ y ∈ Q, y) + 1 = ∑ y ∈ P, y := by
  obtain ⟨x, hxP, hx0, hx1, rfl⟩ := h
  have hne : x - 1 ∉ P.erase x := fun hmem => hx1 (mem_of_mem_erase hmem)
  have hP : x + ∑ y ∈ P.erase x, y = ∑ y ∈ P, y :=
    Finset.add_sum_erase P (fun y => y) hxP
  rw [sum_insert hne]
  omega

/-- `range k` admits no descent: every nonzero element has its predecessor already
occupied. -/
theorem not_isDescent_range (k : ℕ) : ∀ Q, ¬ IsDescent (range k) Q := by
  intro Q ⟨x, hxP, hx0, hx1, _⟩
  rw [mem_range] at hxP
  exact hx1 (mem_range.mpr (by omega))

/-- If no descent is available then `P` is closed under taking predecessors. -/
private theorem pred_mem_of_no_descent (h : ∀ Q, ¬ IsDescent P Q) :
    ∀ x ∈ P, x ≠ 0 → x - 1 ∈ P := by
  intro x hxP hx0
  by_contra hx1
  exact h _ ⟨x, hxP, hx0, hx1, rfl⟩

/-- If no descent is available then `P` is downward closed. -/
private theorem mem_of_le_of_no_descent (h : ∀ Q, ¬ IsDescent P Q) :
    ∀ x ∈ P, ∀ y ≤ x, y ∈ P := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hxP y hy
    rcases eq_or_lt_of_le hy with rfl | hlt
    · exact hxP
    · have hx0 : x ≠ 0 := by omega
      have hpred : x - 1 ∈ P := pred_mem_of_no_descent h x hxP hx0
      exact ih (x - 1) (by omega) hpred y (by omega)

/-- **Descent-free means an initial segment.** A finite set of naturals admits no descent
exactly when it is `range` of its own cardinality. Together with `not_isDescent_range` this pins
the unique terminal configuration, which is what makes the count of descents exact rather than
merely an upper bound. -/
theorem eq_range_of_no_descent (h : ∀ Q, ¬ IsDescent P Q) : P = range P.card := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hmem : P.max' hne ∈ P := P.max'_mem hne
    have hsub : range (P.max' hne + 1) ⊆ P := by
      intro y hy
      exact mem_of_le_of_no_descent h _ hmem y (by simpa [Nat.lt_succ_iff] using hy)
    have hsup : P ⊆ range (P.max' hne + 1) := by
      intro y hy
      exact mem_range.mpr (by have := P.le_max' y hy; omega)
    have : P = range (P.max' hne + 1) := Subset.antisymm hsup hsub
    rw [this, card_range]

/-- A set of `k` distinct naturals has sum at least `0 + 1 + ⋯ + (k - 1)`, the sum over the
descent-free configuration of that size. -/
theorem sum_range_card_le_sum (P : Finset ℕ) :
    ∑ j ∈ range P.card, j ≤ ∑ x ∈ P, x := by
  induction P using Finset.strongInduction with
  | _ P ih =>
    rcases P.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hmem : P.max' hne ∈ P := P.max'_mem hne
      have hsup : P ⊆ range (P.max' hne + 1) := by
        intro y hy
        exact mem_range.mpr (by have := P.le_max' y hy; omega)
      have hcard : P.card ≤ P.max' hne + 1 := by
        have := card_le_card hsup
        simpa using this
      have hpos : 1 ≤ P.card := card_pos.mpr hne
      have herase : ∑ j ∈ range (P.erase (P.max' hne)).card, j
          ≤ ∑ x ∈ P.erase (P.max' hne), x := ih _ (erase_ssubset hmem)
      rw [card_erase_of_mem hmem] at herase
      have hsum : P.max' hne + ∑ x ∈ P.erase (P.max' hne), x = ∑ x ∈ P, x :=
        Finset.add_sum_erase P (fun y => y) hmem
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P.card ≠ 0)
      rw [hk] at herase hcard ⊢
      simp only [Nat.succ_sub_one] at herase
      rw [sum_range_succ]
      omega

/-- `DescentChain n P Q`: `Q` is reachable from `P` by exactly `n` descents. -/
inductive DescentChain : ℕ → Finset ℕ → Finset ℕ → Prop
  | refl (P : Finset ℕ) : DescentChain 0 P P
  | step {n : ℕ} {P Q R : Finset ℕ} :
      IsDescent P Q → DescentChain n Q R → DescentChain (n + 1) P R

/-- Cardinality is a chain invariant. -/
theorem DescentChain.card_eq (h : DescentChain n P Q) : Q.card = P.card := by
  induction h with
  | refl => rfl
  | step hd _ ih => rw [ih, hd.card_eq]

/-- The chain length is exactly the drop in the sum. This is the conservation law the whole
count rests on. -/
theorem DescentChain.sum_add (h : DescentChain n P Q) :
    (∑ y ∈ Q, y) + n = ∑ y ∈ P, y := by
  induction h with
  | refl => simp
  | step hd _ ih => rw [← hd.sum_succ, ← ih]; omega

/-- No chain of descents from `P` is longer than `∑ P - ∑ range P.card`. -/
@[zf_tag "lem_bead_moves"]
theorem DescentChain.length_le (h : DescentChain n P Q) :
    n ≤ (∑ x ∈ P, x) - ∑ j ∈ range P.card, j := by
  have hsum := h.sum_add
  have hcard := h.card_eq
  have hlow : ∑ j ∈ range P.card, j ≤ ∑ y ∈ Q, y := by
    have := sum_range_card_le_sum Q
    rwa [hcard] at this
  omega

/-- Attainment, by strong induction on `∑ P`. -/
private theorem exists_descentChain_aux : ∀ s : ℕ, ∀ P : Finset ℕ, (∑ x ∈ P, x) = s →
    DescentChain ((∑ x ∈ P, x) - ∑ j ∈ range P.card, j) P (range P.card) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro P hP
    by_cases hd : ∀ Q, ¬ IsDescent P Q
    · have hrange := eq_range_of_no_descent hd
      have hz : (∑ x ∈ P, x) - ∑ j ∈ range P.card, j = 0 := by rw [hrange]; simp
      rw [hz, ← hrange]
      exact DescentChain.refl P
    · obtain ⟨Q, hQ⟩ : ∃ Q, IsDescent P Q := by
        by_contra h
        exact hd fun Q hQ => h ⟨Q, hQ⟩
      have hsq : (∑ y ∈ Q, y) + 1 = ∑ y ∈ P, y := hQ.sum_succ
      have hcq : Q.card = P.card := hQ.card_eq
      have hlow : ∑ j ∈ range P.card, j ≤ ∑ y ∈ Q, y := by
        have := sum_range_card_le_sum Q
        rwa [hcq] at this
      have hrec := ih (∑ y ∈ Q, y) (by omega) Q rfl
      rw [hcq] at hrec
      have hlen : (∑ x ∈ P, x) - ∑ j ∈ range P.card, j
          = ((∑ y ∈ Q, y) - ∑ j ∈ range P.card, j) + 1 := by omega
      rw [hlen]
      exact DescentChain.step hQ hrec

/-- **Attainment.** There is a chain from `P` of length exactly `∑ P - ∑ range P.card`, and it
ends at the unique descent-free configuration `range P.card`. With `DescentChain.length_le` this
makes that number the maximum. -/
@[zf_tag "lem_bead_moves"]
theorem exists_descentChain_to_range (P : Finset ℕ) :
    DescentChain ((∑ x ∈ P, x) - ∑ j ∈ range P.card, j) P (range P.card) :=
  exists_descentChain_aux _ P rfl

end ZeroFree
