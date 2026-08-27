/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.AlmostAll
public import ZeroFree.CountD

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace ZeroFree.Challenge

/-- **`thm_pointwise` — the pointwise bound.** `D(n) ≤ C n^{3/4}` for every `n ≥ 1`,
with a single constant `C` quantified outside `n`. The exponent is `Real.rpow`. -/
theorem thm_pointwise (L : LiteratureInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (D n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 4) :=
  exists_pointwise_bound L

/-- **`thm_almostall` — the almost-all bound.** For `B > 5/6` some `C_B > 0` has:
for every `ε > 0` there is a `C > 0` with

    #{ 1 ≤ n ≤ X : D(n) > C_B n^{1/2} (log n)^B } ≤ C X (log X)^{-(1/2)(B-5/6)+ε}

for every `X ≥ 3`. `C_B` is chosen *before* `ε`, so the threshold is a fixed one. -/
theorem thm_almostall (L : LiteratureInputs) {B : ℝ} (hB : 5 / 6 < B) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n : ℕ => CB * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ B
            < (D n : ℝ))).card : ℝ)
        ≤ C * X * Real.log X ^ (-(1 / 2 : ℝ) * (B - 5 / 6) + ε) :=
  exists_almostall_bound L hB

end ZeroFree.Challenge
