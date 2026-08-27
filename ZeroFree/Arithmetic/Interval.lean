/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import ZeroFree.Meta.Attr

/-!
# The search interval in the 3-core distance bound

For `N ≥ 81` the interval `[√(N - 27T²), √N]`, where `T = ⌊N^{1/4}⌋`, is longer than `9`, and so
contains an integer in any prescribed residue class mod `9`.

## Main results

* `interval_length`: `N - 27⌊N^{1/4}⌋² < (√N - 9)²` for every real `N ≥ 81`.
-/

@[expose] public section

namespace ZeroFree

open Real

/-- For `N ≥ 81`, `N - 27⌊N^{1/4}⌋² < (√N - 9)²`. Equivalently, the interval
`[√(N - 27⌊N^{1/4}⌋²), √N]` is longer than `9`; the squared form mentions no square root of a
quantity whose sign has still to be established.

Substituting `x = N^{1/4}`, so that `N = x⁴` and `√N = x²`, the claim is `27T² > 18x² - 81` where
`T = ⌊x⌋`. Since `T > x - 1 ≥ 2`, it suffices that `27(x-1)² ≥ 18x² - 81`, and that difference is
`9(x-3)² + 27`. The threshold `81` is what makes `√N - 9` nonnegative. -/
@[zf_tag "lem_interval_length"]
theorem interval_length {N : ℝ} (hN : 81 ≤ N) :
    N - 27 * (⌊N ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ^ 2 < (Real.sqrt N - 9) ^ 2 := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set x : ℝ := N ^ ((1 : ℝ) / 4) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0 _
  have hsq : Real.sqrt N = x ^ 2 := by
    rw [Real.sqrt_eq_rpow, hxdef, ← Real.rpow_natCast (N ^ ((1 : ℝ) / 4)) 2,
      ← Real.rpow_mul hN0]
    norm_num
  have hN4 : N = x ^ 4 := by
    have := Real.sq_sqrt hN0
    rw [hsq] at this
    nlinarith [this]
  have hx3 : 3 ≤ x := by
    have h81 : (81 : ℝ) ^ ((1 : ℝ) / 4) = 3 := by
      rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast 3 4,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    have hmono : (81 : ℝ) ^ ((1 : ℝ) / 4) ≤ N ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hN (by norm_num)
    rw [h81] at hmono
    rw [hxdef]
    exact hmono
  have hTx : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hTsq : (x - 1) ^ 2 < (⌊x⌋₊ : ℝ) ^ 2 := by nlinarith [hTx, hx3]
  rw [hsq, hN4]
  nlinarith [hTsq, sq_nonneg (x - 3), hx3]

end ZeroFree
