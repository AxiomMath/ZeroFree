/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ZeroFree.Meta.Attr

/-!
# Triangular and Loeschian numbers

The triangular numbers `T_u = u(u+1)/2` and the Loeschian numbers, the positive natural numbers
represented by the Eisenstein norm form `x² + xy + y²`. Every integer of the shape `A² + 27y²` is
a value of that form; the Loeschian numbers are closed under multiplication, because a norm form
composes; and `1`, `4` and `7` are Loeschian, so `3m + 1` is Loeschian for every `m < 3`.

## Main definitions

* `tri`: the `u`-th triangular number `u(u+1)/2`.
* `Loeschian`: a positive natural number of the form `x² + xy + y²` with `x, y : ℤ`.

## Main results

* `two_mul_tri`: `2 T_u = u(u+1)`.
* `sq_add_twentySeven_mul_sq`: `A² + 27y²` is a value of the Eisenstein norm form.
* `Loeschian.mul`: the Loeschian numbers are closed under multiplication.
* `loeschian_one`, `loeschian_four`, `loeschian_seven`: `1`, `4` and `7` are Loeschian.
* `loeschian_three_mul_add_one_of_lt_three`: `3m + 1` is Loeschian for every `m < 3`.
-/

@[expose] public section

namespace ZeroFree

/-- The `u`-th triangular number `T_u = u(u+1)/2`. -/
@[zf_tag "def_triangular"]
def tri (u : ℕ) : ℕ := u * (u + 1) / 2

/-- `tri` without the division: `2 T_u = u(u+1)`. -/
theorem two_mul_tri (u : ℕ) : 2 * tri u = u * (u + 1) := by
  rw [tri]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self u).two_dvd

/-- A natural number is *Loeschian* when it is a positive value of the Eisenstein norm form
`x^2 + xy + y^2`. -/
@[zf_tag "def_loeschian"]
def Loeschian (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ x y : ℤ, (m : ℤ) = x ^ 2 + x * y + y ^ 2

/-- Every integer of the form `A^2 + 27 y^2` is a value of the Eisenstein norm form, at
`(x, y) = (A - 3y, 6y)`. -/
@[zf_tag "lem_loeschian_shape"]
theorem sq_add_twentySeven_mul_sq (A y : ℤ) :
    A ^ 2 + 27 * y ^ 2 = (A - 3 * y) ^ 2 + (A - 3 * y) * (6 * y) + (6 * y) ^ 2 := by
  ring

/-- `1` is Loeschian, via `(x,y) = (1,0)`. -/
@[zf_tag "lem_loeschian_147"]
theorem loeschian_one : Loeschian 1 := ⟨le_refl 1, 1, 0, by norm_num⟩

/-- `4` is Loeschian, via `(x,y) = (2,0)`. -/
@[zf_tag "lem_loeschian_147"]
theorem loeschian_four : Loeschian 4 := ⟨by norm_num, 2, 0, by norm_num⟩

/-- `7` is Loeschian, via `(x,y) = (2,1)`. -/
@[zf_tag "lem_loeschian_147"]
theorem loeschian_seven : Loeschian 7 := ⟨by norm_num, 2, 1, by norm_num⟩

/-- **Loeschian numbers are closed under multiplication.** The Eisenstein form `Q` is a norm
form, so it composes: `Q(x₁,y₁) · Q(x₂,y₂) = Q(x₁x₂ - y₁y₂, x₁y₂ + y₁x₂ + y₁y₂)`.

The sign of the middle coefficient is what distinguishes this from the composition law of
`x² - xy + y²`: at `m = n = 3` with `x₁ = y₁ = x₂ = y₂ = 1` the formula above gives
`Q(0, 3) = 9`, while `y₃ = x₁y₂ + y₁x₂ - y₁y₂` would give `Q(0, 1) = 1`. -/
theorem Loeschian.mul {m n : ℕ} (hm : Loeschian m) (hn : Loeschian n) :
    Loeschian (m * n) := by
  obtain ⟨hm1, x₁, y₁, hxy₁⟩ := hm
  obtain ⟨hn1, x₂, y₂, hxy₂⟩ := hn
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    x₁ * x₂ - y₁ * y₂, x₁ * y₂ + y₁ * x₂ + y₁ * y₂, ?_⟩
  push_cast
  rw [hxy₁, hxy₂]
  ring

/-- For every residue `m < 3`, the shifted value `3m + 1` is Loeschian: these are `1`, `4`
and `7`. -/
@[zf_tag "lem_loeschian_147"]
theorem loeschian_three_mul_add_one_of_lt_three {m : ℕ} (hm : m < 3) :
    Loeschian (3 * m + 1) := by
  interval_cases m
  · simpa using loeschian_one
  · simpa using loeschian_four
  · simpa using loeschian_seven

end ZeroFree
