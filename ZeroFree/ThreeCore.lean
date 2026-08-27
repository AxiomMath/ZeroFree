/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Arithmetic.LegendreThree
public import ZeroFree.LiteratureInputs
public import ZeroFree.Meta.Attr

/-!
# The `3`-core criterion

A `3`-core of size `m` exists exactly when `3m + 1` is a Loeschian number, that is, a value of the
Eisenstein norm form `x² + xy + y²`.

The count of the `3`-cores of size `m` as the divisor sum `∑_{d ∣ 3m+1} (d/3)` is a
generating-function identity of Granville–Ono, admitted as `LiteratureInputs.threeCoreCount`.
What turns that count into the criterion is proved: the divisor sum factors into local factors
(`legThreeZeta_isMultiplicative`), each of which is `e + 1` at a prime `≡ 1 mod 3` and `1` or `0`
at a prime `≡ 2 mod 3`, so the sum is positive exactly when every prime `≡ 2 mod 3` occurs to an
even power (`sum_divisors_legendreSym_pos_iff`) — which is the condition characterizing the
Loeschian numbers.

## Main results

* `exists_isTCore_three_iff`: a `3`-core of size `m` exists iff `3m + 1` is Loeschian.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- A `3`-core of size `m` exists exactly when `3m + 1` is Loeschian.

The bead-set normalization (`card = m` and `beadSize = m`) is the one used throughout: a partition
of `m` has at most `m` parts, so pinning the bead count represents every partition of `m` exactly
once. -/
@[zf_tag "lem_3core"]
theorem exists_isTCore_three_iff (L : LiteratureInputs) (m : ℕ) :
    (∃ S : BeadSet, S.card = m ∧ beadSize S = m ∧ IsTCore 3 S)
      ↔ Loeschian (3 * m + 1) := by
  classical
  have hfin := finite_beadSets_card_size 3 m
  have hcnt : (0 < {S : BeadSet | S.card = m ∧ beadSize S = m ∧ IsTCore 3 S}.ncard)
      ↔ (0 < ∑ d ∈ (3 * m + 1).divisors, legendreSym 3 (d : ℤ)) := by
    rw [← L.threeCoreCount m]
    exact (Nat.cast_pos (α := ℤ)).symm
  have harith : (0 < ∑ d ∈ (3 * m + 1).divisors, legendreSym 3 (d : ℤ))
      ↔ Loeschian (3 * m + 1) :=
    (sum_divisors_legendreSym_pos_iff (n := 3 * m + 1) (by omega) (by omega)).trans
      (L.eisenstein (by omega)).symm
  refine Iff.trans ?_ (hcnt.trans harith)
  rw [Set.ncard_pos hfin]
  exact ⟨fun ⟨S, hS⟩ => ⟨S, hS⟩, fun ⟨S, hS⟩ => ⟨S, hS⟩⟩

end ZeroFree
