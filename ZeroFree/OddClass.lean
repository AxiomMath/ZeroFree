/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Abacus.SelfConj
public import ZeroFree.SignTwist
public import ZeroFree.Meta.Attr

/-!
# Odd classes are not zero-free

If every part of `μ` lies in `{1, 2, 3}` and the number of parts equal to `2` is odd, then some
`λ` has `χ^λ(μ) = 0`.

At a self-conjugate `S` the sign twist reads `χ^S(w) = (-1)^{n-k} χ^S(w)`, so an odd `n - k`
forces `χ^S(w) = 0`; nothing about the partition matters beyond its being a fixed point of the
transpose. With `a`, `b`, `c` the numbers of parts equal to `3`, `2`, `1`, the exponent is

  `w.sum + w.length = (3a + 2b + c) + (a + b + c) = 4a + 3b + 2c ≡ b  (mod 2)`

so it is odd exactly when `b` is.

## Main results

* `sum_add_length_mod_two`: for parts drawn from `{1, 2, 3}`, `sum + length` and the number of
  parts equal to `2` have the same parity.
* `exists_chi_eq_zero_of_odd_twos`: such a class with an odd number of parts equal to `2` is not
  zero-free.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- For a list of parts drawn from `{1, 2, 3}`, `sum + length` has the same parity as the number of
parts equal to `2`. -/
theorem sum_add_length_mod_two :
    ∀ w : List ℕ, (∀ t ∈ w, t = 1 ∨ t = 2 ∨ t = 3) →
      (w.sum + w.length) % 2 = (w.count 2) % 2 := by
  intro w
  induction w with
  | nil => intro _; simp
  | cons t u ih =>
    intro hw
    have ht : t = 1 ∨ t = 2 ∨ t = 3 := hw t (List.mem_cons_self ..)
    have hu : ∀ s ∈ u, s = 1 ∨ s = 2 ∨ s = 3 := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    have hrec := ih hu
    simp only [List.sum_cons, List.length_cons, List.count_cons]
    -- A part of size `1` or `3` moves `sum + length` by an even amount and leaves `count 2`
    -- fixed; a part of size `2` moves it by `3` and increments the count.
    rcases ht with rfl | rfl | rfl <;> simp <;> omega

/-- A class with every part in `{1, 2, 3}` and an odd number of parts equal to `2` is not
zero-free: the character value vanishes at some self-conjugate bead set. -/
@[zf_tag "lem_odd_class"]
theorem exists_chi_eq_zero_of_odd_twos {w : List ℕ}
    (hw : ∀ t ∈ w, t = 1 ∨ t = 2 ∨ t = 3) (hodd : w.count 2 % 2 = 1)
    (hn : 3 ≤ w.sum) :
    ∃ S : BeadSet, beadSize S = w.sum ∧ chi S w = 0 := by
  classical
  obtain ⟨S, hsub, hsize, hfix⟩ := exists_selfconj hn
  refine ⟨S, hsize, ?_⟩
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t htw
    rcases hw t htw with rfl | rfl | rfl <;> omega
  have hpar : (w.sum + w.length) % 2 = 1 := by
    rw [sum_add_length_mod_two w hw]; exact hodd
  have hsign : ((-1 : ℤ)) ^ (w.sum + w.length) = -1 :=
    Odd.neg_one_pow (Nat.odd_iff.mpr hpar)
  have htw := chi_transpose w hpos S hsub
  rw [hfix, hsign] at htw
  linarith [htw]

end ZeroFree
