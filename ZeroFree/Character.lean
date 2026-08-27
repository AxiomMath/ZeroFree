/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import ZeroFree.Abacus.Beads
public import ZeroFree.Meta.Attr

/-!
# The character value, the zero-free condition, and `D(n)`

## Main definitions

* `ZeroFree.chi`: the Murnaghan–Nakayama value `χ^S(w)` of a bead set `S` at a list `w` of part
  sizes.
* `ZeroFree.ZeroFreeColumn`: the column of the character table of `S n` indexed by a partition `μ`
  of `n` is zero-free when no irreducible character vanishes on it.
* `ZeroFree.D`: the number of zero-free columns of the character table of `S n`.

## Main results

* `ZeroFree.chi_eq_zero_of_isTCore`: a `t`-core annihilates any class whose first part is `t`.

## `chi` is a definition

Mathlib has no Specht modules and no symmetric-group character theory, so there is no ambient
`χ^λ(μ)` to be faithful to: `chi` is **defined** by the Murnaghan–Nakayama recursion of James and
Kerber, *The Representation Theory of the Symmetric Group*, Theorem 2.4.7. It is total and
computable.

The cost is concentrated in one place: everything said here about "the character table of `S_n`"
rests on this definition being the real Murnaghan–Nakayama rule. That is why it is written out
unfolded in `Comparator/Challenge.lean`, where a mathematician can read it without following the
library.

## Recursion on a list, not a multiset

`chi` recurses on a *list* of part sizes, structurally: the tail is shorter, so termination is
free. The price is that invariance under reordering the list is a theorem (`ZeroFree.chi_perm`)
rather than true by construction.

## Why partitions of `n` are bead sets of card `n`

A bead set determines a partition, but not conversely a unique bead set: padding `λ` with a zero
part sends `β_m(λ)` to `{0} ∪ (β_m(λ) + 1)`. Rather than quotient by that, `ZeroFreeColumn` and
`D` quantify over bead sets of card exactly `n`. This is a normalization, not a restriction: a
partition of `n` has at most `n` parts, so every one of them is represented, exactly once, at card
`n`. It avoids needing padding-invariance of `chi` as a prerequisite to even *stating* the results.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- The Murnaghan–Nakayama value `χ^S(w)`, defined by recursion on the list `w` of part sizes.

The empty list gives `1` on the empty diagram and `0` otherwise. A nonempty list `t :: v` sums over
the rim hooks of length `t`, each contributing its sign `(-1)^{ht}` times the value on the removal.

The rim hooks, their heights and the removal are the bead-set notions of `Abacus/Beads.lean`, so
this is the rule in its standard abacus form. -/
@[zf_tag "def_chi"]
noncomputable def chi (S : BeadSet) : List ℕ → ℤ
  | [] => if beadSize S = 0 then 1 else 0
  | t :: v =>
      ∑ x ∈ S.filter (fun x => t ≤ x ∧ x - t ∉ S),
        (-1) ^ (rimHookHeight t S x) * chi (rimHookRemoval t S x) v

/-- `chi` at a nonempty list `t :: v`: the signed sum over the rim hooks of length `t` in `S`. -/
theorem chi_cons (S : BeadSet) (t : ℕ) (v : List ℕ) :
    chi S (t :: v) =
      ∑ x ∈ S.filter (fun x => t ≤ x ∧ x - t ∉ S),
        (-1) ^ (rimHookHeight t S x) * chi (rimHookRemoval t S x) v := rfl

/-- The filter in `chi_cons` is exactly the set of rim hooks of length `t`. -/
theorem mem_chi_filter {S : BeadSet} {t x : ℕ} :
    x ∈ S.filter (fun x => t ≤ x ∧ x - t ∉ S) ↔ IsRimHook t S x := by
  simp only [Finset.mem_filter, IsRimHook]

/-- `chi` on the empty list vanishes unless the diagram is empty. -/
theorem chi_nil (S : BeadSet) : chi S [] = if beadSize S = 0 then 1 else 0 := rfl

/-- A column of the character table is *zero-free* when no partition of `n` gives the value `0`.

Partitions of `n` are the bead sets of card `n` with `beadSize = n`; see the module docstring for
why the card is pinned. -/
@[zf_tag "def_zerofree"]
def ZeroFreeColumn (n : ℕ) (μ : Nat.Partition n) : Prop :=
  ∀ S : BeadSet, S.card = n → beadSize S = n → chi S μ.parts.toList ≠ 0

open scoped Classical in
/-- `D n`, the number of zero-free columns of the character table of `S n`. -/
@[zf_tag "def_D"]
noncomputable def D (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun μ : Nat.Partition n => ZeroFreeColumn n μ)).card

/-- **A `t`-core annihilates any class led by `t`.** The Murnaghan–Nakayama sum is indexed by the
rim hooks of length `t`, and a `t`-core has none, so the sum is empty. -/
theorem chi_eq_zero_of_isTCore {t : ℕ} {S : BeadSet} (h : IsTCore t S) (v : List ℕ) :
    chi S (t :: v) = 0 := by
  rw [chi_cons]
  refine Finset.sum_eq_zero ?_
  intro x hx
  exact absurd (mem_chi_filter.mp hx) (h x)

end ZeroFree
