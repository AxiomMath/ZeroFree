/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import ZeroFree.Tail
public import ZeroFree.CountD

/-!
# The almost-all bound

For `B > 5/6` there is a constant `C_B > 0` such that, for every `ε > 0`,

`#{1 ≤ n ≤ X : D(n) > C_B n^{1/2} (log n)^B} ≤ C_{B,ε} X (log X)^{-(B - 5/6)/2 + ε}`

for every `X ≥ 3`. The constant is `C_B = 2^{B+1}(C₂+1)`, where `C₂` is the constant of `s2_bound`,
and its `2^B` is the exact cost of `log X ≤ 2 log n` on the range `n ≥ √X`. It is bound *outside*
the `∀ ε`, so the display bounds one fixed exceptional set rather than a family of them.

## Main results

* `gamma_spec`: the `γ` construction, with the exponent identity
  `5/6 (γ-1) - B (γ-1) = -(B - 5/6)/2 + ε` that converts the tail estimate's exponent into the one
  above.
* `log_rpow_le_mul`, `log_rpow_le_mul_sqrt`: `(log X)^a ≤ a^a X` and `(log X)^a ≤ 2^a a^a √X`.
* `rpow_floor_bound`, `main_term_bound`: replacing `(log X)^B` by `⌊(log X)^B⌋₊` costs at most a
  factor `2^(γ-1)`, and the tail estimate's main term then carries the exponent above.
* `D_le_of_s3_le`: `s₃(n) ≤ K (log n)^B` implies `D n ≤ 2K(C₂+1) √n (log n)^B`.
* `log_le_two_mul_log_of_sqrt_le`, `log_rpow_lt_s3_of_D_gt`: the bridge from the per-`n` threshold
  to the uniform one, on the range `n ≥ √X`.
* `exists_almostall_bound`: the bound above.
* `density_tendsto_zero`: the exceptional set has density zero.
-/

@[expose] public section

namespace ZeroFree

open Filter

/-- **The `γ` construction.** For `5/6 < B` and `0 < ε < (B - 5/6)/2`, set
`γ = 3/2 - ε/(B - 5/6)`. Then `γ` lies strictly in `(1, 3/2)` — the range `tail_bound` requires —
and it converts the tail estimate's exponent into the almost-all bound's.

The exponent identity is the load-bearing part. `tail_bound` supplies a factor
`(log X) ^ (5/6 * (γ - 1))` and the `S^(1-γ)` bound contributes `(log X) ^ (B * (1 - γ))`; their
product carries exponent `5/6 * (γ - 1) - B * (γ - 1)`, and this lemma says that equals
`-(B - 5/6)/2 + ε`.

The upper bound `γ < 3/2` is where `ε < (B - 5/6)/2` is spent, and the lower bound `1 < γ` is where
it is spent again, via `ε/(B - 5/6) < 1/2`.

`5/6 < B` is *not* a hypothesis: it follows from `0 < ε < (B - 5/6)/2`. -/
theorem gamma_spec {B ε : ℝ} (hε : 0 < ε) (hεB : ε < (B - 5 / 6) / 2) :
    ∃ γ : ℝ, 1 < γ ∧ γ < 3 / 2 ∧
      5 / 6 * (γ - 1) - B * (γ - 1) = -(B - 5 / 6) / 2 + ε := by
  have hBpos : 0 < B - 5 / 6 := by linarith
  refine ⟨3 / 2 - ε / (B - 5 / 6), ?_, ?_, ?_⟩
  · -- `ε / (B - 5/6) < 1/2`, so `γ > 3/2 - 1/2 = 1`.
    have : ε / (B - 5 / 6) < 1 / 2 := by
      rw [div_lt_iff₀ hBpos]; linarith
    linarith
  · -- `ε > 0` makes the subtracted term positive.
    have : 0 < ε / (B - 5 / 6) := div_pos hε hBpos
    linarith
  · -- `γ - 1 = 1/2 - ε/(B - 5/6)`, and `(5/6 - B) * (γ - 1) = -(B - 5/6)(γ - 1)`.
    have hne : B - 5 / 6 ≠ 0 := ne_of_gt hBpos
    -- Cancel the denominator once.
    have hcancel : (B - 5 / 6) * (ε / (B - 5 / 6)) = ε := by
      rw [mul_comm]; exact div_mul_cancel₀ ε hne
    have hexp : 5 / 6 * (3 / 2 - ε / (B - 5 / 6) - 1)
        - B * (3 / 2 - ε / (B - 5 / 6) - 1)
        = -(B - 5 / 6) / 2 + (B - 5 / 6) * (ε / (B - 5 / 6)) := by ring
    rw [hexp, hcancel]


/-- **A power of the logarithm is dominated by the argument.** For `a > 0` and `X ≥ 1`,
`(log X) ^ a ≤ a ^ a * X`.

`Real.log_le_rpow_div` gives `log X ≤ X ^ δ / δ` for every `δ > 0`; taking `δ = 1/a` and raising to
the `a` turns `X ^ (1/a)` into `X` exactly. Choosing `δ` freely is the whole trick —
`log X ≤ X - 1` would only give `(log X)^a ≤ X^a`, useless once `a > 1`, and `a` is as large as
`B + (B - 5/6)/2` in the almost-all bound. -/
theorem log_rpow_le_mul {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) :
    Real.log X ^ a ≤ a ^ a * X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX
  -- `log X ≤ X ^ (1/a) * a`, which is `Real.log_le_rpow_div` at `δ = 1/a`.
  have h : Real.log X ≤ X ^ (1 / a) * a := by
    have h' := Real.log_le_rpow_div hX0 (by positivity : (0:ℝ) < 1 / a)
    have hane : a ≠ 0 := ha.ne'
    -- `u / (1/a) = u * a`.
    have heq : X ^ (1 / a) / (1 / a) = X ^ (1 / a) * a := by field_simp
    rwa [heq] at h'
  have hXa : (0 : ℝ) ≤ X ^ (1 / a) := Real.rpow_nonneg hX0 _
  calc Real.log X ^ a ≤ (X ^ (1 / a) * a) ^ a := Real.rpow_le_rpow hlog0 h ha.le
    _ = (X ^ (1 / a)) ^ a * a ^ a := Real.mul_rpow hXa ha.le
    _ = a ^ a * X := by
        rw [← Real.rpow_mul hX0, one_div_mul_cancel ha.ne', Real.rpow_one]
        ring

/-- **The same domination against `√X`.** For `a > 0` and `X ≥ 1`,
`(log X) ^ a ≤ 2 ^ a * a ^ a * √X`.

The previous lemma applied at `√X`, where `log √X = (log X)/2` supplies the factor `2 ^ a`. -/
theorem log_rpow_le_mul_sqrt {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) :
    Real.log X ^ a ≤ 2 ^ a * a ^ a * Real.sqrt X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt X := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hX
  have hhalf : Real.log X = 2 * Real.log (Real.sqrt X) := by
    rw [Real.log_sqrt hX0.le]; ring
  have hl0 : (0 : ℝ) ≤ Real.log (Real.sqrt X) := Real.log_nonneg hs1
  have hkey := log_rpow_le_mul ha hs1
  have h2a : (0 : ℝ) ≤ (2 : ℝ) ^ a := (Real.rpow_pos_of_pos (by norm_num) a).le
  calc Real.log X ^ a = (2 * Real.log (Real.sqrt X)) ^ a := by rw [hhalf]
    _ = 2 ^ a * Real.log (Real.sqrt X) ^ a := Real.mul_rpow (by norm_num) hl0
    _ ≤ 2 ^ a * (a ^ a * Real.sqrt X) := by
        exact mul_le_mul_of_nonneg_left hkey h2a
    _ = 2 ^ a * a ^ a * Real.sqrt X := by ring


/-- **The `S`-bound.** With `S = ⌊(log X)^B⌋₊`, once `(log X)^B ≥ 1` we have `S ≥ (log X)^B / 2`,
and therefore `S ^ (1 - γ) ≤ 2 ^ (γ - 1) * (log X) ^ (B * (1 - γ))` for `γ > 1`.

The direction is the subtle part: `1 - γ < 0`, so `u ↦ u ^ (1 - γ)` is **decreasing**, and a
*lower* bound on `S` is what yields an *upper* bound on `S ^ (1 - γ)`. The obvious upper bound
`S ≤ (log X)^B` gives an inequality pointing the wrong way, which cannot be combined with
`tail_bound`.

The `2 ^ (γ - 1)` factor is the price of `⌊·⌋₊` losing at most a factor of two, and it is absorbed
into the final constant.

The hypothesis is `1 ≤ L ^ B`, not `2 ≤ L ^ B`. Both give `L^B/2 ≤ ⌊L^B⌋₊`, but for different
reasons: above `2` because `⌊u⌋₊ > u - 1 ≥ u/2`, and on `[1,2)` because `⌊u⌋₊ = 1 ≥ u/2`. The
weaker hypothesis is what keeps a separate small-`X` case out of the final assembly, since
`1 ≤ (log X)^B` holds for *every* `X ≥ 3` whereas `2 ≤ (log X)^B` fails on `[3, e^{2^{1/B}})`. -/
theorem rpow_floor_bound {B γ L : ℝ} (hγ : 1 < γ) (hL : 0 < L) (h1 : 1 ≤ L ^ B) :
    (⌊L ^ B⌋₊ : ℝ) ^ (1 - γ) ≤ 2 ^ (γ - 1) * (L ^ B) ^ (1 - γ) := by
  have hLB : (0 : ℝ) < L ^ B := by positivity
  -- `⌊L^B⌋₊ ≥ L^B / 2`, by cases on whether `L^B` has reached `2`.
  have hfloor : L ^ B / 2 ≤ (⌊L ^ B⌋₊ : ℝ) := by
    rcases le_or_gt (L ^ B) 2 with hle | hgt
    · -- On `[1, 2]` the floor is at least `1`, and `L^B/2 ≤ 1`.
      have hfl1 : (1 : ℕ) ≤ ⌊L ^ B⌋₊ := Nat.le_floor (by exact_mod_cast h1)
      have : (1 : ℝ) ≤ (⌊L ^ B⌋₊ : ℝ) := by exact_mod_cast hfl1
      linarith
    · -- Above `2`, `⌊u⌋₊ > u - 1 ≥ u/2`.
      have hlt : L ^ B - 1 < (⌊L ^ B⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (L ^ B)
        linarith
      linarith
  have hpos : (0 : ℝ) < L ^ B / 2 := by linarith
  have hexp : 1 - γ ≤ 0 := by linarith
  -- Antitone in the base at a nonpositive exponent: the LOWER bound on the floor
  -- is what bounds its `(1 - γ)` power from ABOVE.
  have hanti : (⌊L ^ B⌋₊ : ℝ) ^ (1 - γ) ≤ (L ^ B / 2) ^ (1 - γ) :=
    Real.rpow_le_rpow_of_nonpos hpos hfloor hexp
  -- `(u/2)^(1-γ) = 2^(γ-1) * u^(1-γ)`, since `2^(γ-1) = (2^(1-γ))⁻¹`.
  have hsplit : (L ^ B / 2) ^ (1 - γ) = 2 ^ (γ - 1) * (L ^ B) ^ (1 - γ) := by
    rw [Real.div_rpow hLB.le (by norm_num : (0:ℝ) ≤ 2)]
    have hinv : (2:ℝ) ^ (γ - 1) = ((2:ℝ) ^ (1 - γ))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [hinv]
    field_simp
  rw [hsplit] at hanti
  exact hanti


/-- **The main term.** The tail estimate's dominant summand, evaluated at `S = ⌊L^B⌋₊`, already
carries the almost-all bound's exponent.

`tail_bound` supplies `X * L ^ (5/6 * (γ - 1)) * S ^ (1 - γ)`. Substituting the floor and applying
`rpow_floor_bound` replaces `S ^ (1 - γ)` by `2 ^ (γ - 1) * L ^ (B * (1 - γ))`, and then the two
powers of `L` merge:

`5/6 * (γ - 1) + B * (1 - γ) = 5/6 * (γ - 1) - B * (γ - 1)`

which `gamma_spec` says equals `-(B - 5/6)/2 + ε`. So the whole main term is
`2 ^ (γ - 1) * X * L ^ (-(B - 5/6)/2 + ε)`, with the factor `2 ^ (γ - 1)` bound in terms of `γ`
alone and therefore absorbable.

The exponent identity is a hypothesis rather than recomputed here, so the arithmetic is checked in
exactly one place. -/
theorem main_term_bound {B γ ε L X : ℝ} (hγ : 1 < γ) (hL : 0 < L)
    (h1 : 1 ≤ L ^ B) (hX : 0 ≤ X)
    (hid : 5 / 6 * (γ - 1) - B * (γ - 1) = -(B - 5 / 6) / 2 + ε) :
    X * L ^ ((5 : ℝ) / 6 * (γ - 1)) * (⌊L ^ B⌋₊ : ℝ) ^ (1 - γ)
      ≤ 2 ^ (γ - 1) * (X * L ^ (-(B - 5 / 6) / 2 + ε)) := by
  have hfl := rpow_floor_bound hγ hL h1
  -- `(L^B)^(1-γ) = L^(B*(1-γ))`.
  have hmul : (L ^ B) ^ (1 - γ) = L ^ (B * (1 - γ)) := by
    rw [← Real.rpow_mul hL.le]
  -- The two powers of `L` merge, and the exponent is `-(B - 5/6)/2 + ε`.
  have hadd : L ^ ((5 : ℝ) / 6 * (γ - 1)) * L ^ (B * (1 - γ))
      = L ^ (-(B - 5 / 6) / 2 + ε) := by
    rw [← Real.rpow_add hL]
    congr 1
    linarith [hid]
  have hLpow : (0 : ℝ) < L ^ ((5 : ℝ) / 6 * (γ - 1)) := Real.rpow_pos_of_pos hL _
  have h2γ : (0 : ℝ) ≤ 2 ^ (γ - 1) := (Real.rpow_pos_of_pos (by norm_num) _).le
  calc X * L ^ ((5 : ℝ) / 6 * (γ - 1)) * (⌊L ^ B⌋₊ : ℝ) ^ (1 - γ)
      ≤ X * L ^ ((5 : ℝ) / 6 * (γ - 1)) * (2 ^ (γ - 1) * (L ^ B) ^ (1 - γ)) := by
        have : (0 : ℝ) ≤ X * L ^ ((5 : ℝ) / 6 * (γ - 1)) := by positivity
        exact mul_le_mul_of_nonneg_left hfl this
    _ = 2 ^ (γ - 1) * (X * (L ^ ((5 : ℝ) / 6 * (γ - 1)) * L ^ (B * (1 - γ)))) := by
        rw [hmul]; ring
    _ = 2 ^ (γ - 1) * (X * L ^ (-(B - 5 / 6) / 2 + ε)) := by rw [hadd]


/-- **Where `C_B` comes from, and why it cannot depend on `ε`.** If `s₃(n) ≤ K (log n)^B` for some
`K ≥ 1`, then for `n ≥ 3`

`D n ≤ 2 K (C₂ + 1) * √n * (log n)^B`,

where `C₂` is the constant of `s2_bound`.

`C₂` knows nothing of `ε`, `K` will be `2^B`, and `B` is fixed before `ε` is introduced, so the
resulting `C_B = 2^{B+1}(C₂+1)` is determined by `B` alone. That is *why* `C_B` may be bound
outside the `∀ ε`, and therefore why "almost all `n` satisfy `D(n) ≤ C_B n^{1/2}(log n)^B`" denotes
one set rather than a family of them.

The chain is `D_le_succ_s3_mul_succ_s2` then `s2_bound`:
`D n ≤ (s₃ n + 1)(s₂ n + 1) ≤ (K (log n)^B + 1)(C₂ √n + 1)`, and both `+1`s are absorbed using
`1 ≤ K (log n)^B` and `1 ≤ √n`, which hold for `n ≥ 3`.

The factor `K` is not decoration: the assembly holds `s₃(n) ≤ (log X)^B` at the *uniform* threshold
and converts it with `log X ≤ 2 log n` (see `log_le_two_mul_log_of_sqrt_le`), which costs exactly
`K = 2^B`. -/
theorem D_le_of_s3_le (L : LiteratureInputs) {C₂ K : ℝ}
    (hs2 : ∀ m : ℕ, 1 ≤ m → (s2 m : ℝ) ≤ C₂ * Real.sqrt m)
    {B : ℝ} (hB : 0 ≤ B) (hK : 1 ≤ K) {n : ℕ} (hn : 3 ≤ n)
    (hs3 : (s3 n : ℝ) ≤ K * Real.log n ^ B) :
    (D n : ℝ) ≤ 2 * K * (C₂ + 1) * Real.sqrt n * Real.log n ^ B := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `log n ≥ log 3 > 1`, so `(log n)^B ≥ 1`.
  have hlog1 : (1 : ℝ) ≤ Real.log n := by
    -- `1 ≤ log 3` is `e ≤ 3`; `Real.exp_one_lt_d9` gives `e < 2.7182818286`.
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans h3 (Real.log_le_log (by norm_num) hnR)
  have hLB1 : (1 : ℝ) ≤ Real.log n ^ B := Real.one_le_rpow hlog1 hB
  -- `K (log n)^B ≥ 1`, the fact that absorbs the `+1` on the `s₃` side.
  have hKL : (1 : ℝ) ≤ K * Real.log n ^ B := by nlinarith [hK, hLB1]
  -- `√n ≥ 1`.
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  -- The counting step, cast to `ℝ`.
  have hcount : (D n : ℝ) ≤ ((s3 n : ℝ) + 1) * ((s2 n : ℝ) + 1) := by
    have := D_le_succ_s3_mul_succ_s2 L hn
    have hc : ((D n : ℕ) : ℝ) ≤ (((s3 n + 1) * (s2 n + 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr this
    push_cast at hc
    linarith
  have hs2n := hs2 n hn1
  have hs30 : (0 : ℝ) ≤ (s3 n : ℝ) := Nat.cast_nonneg _
  have hs20 : (0 : ℝ) ≤ (s2 n : ℝ) := Nat.cast_nonneg _
  -- `(s₃+1) ≤ 2 K (log n)^B` and `(s₂+1) ≤ (C₂+1) √n`.
  have hA : (s3 n : ℝ) + 1 ≤ 2 * K * Real.log n ^ B := by linarith
  have hBnd : (s2 n : ℝ) + 1 ≤ (C₂ + 1) * Real.sqrt n := by nlinarith [hs2n, hsq1]
  calc (D n : ℝ) ≤ ((s3 n : ℝ) + 1) * ((s2 n : ℝ) + 1) := hcount
    _ ≤ (2 * K * Real.log n ^ B) * ((C₂ + 1) * Real.sqrt n) :=
        mul_le_mul hA hBnd (by positivity) (by linarith)
    _ = 2 * K * (C₂ + 1) * Real.sqrt n * Real.log n ^ B := by ring


/-- **The uniform-threshold bridge.** For `n ≥ √X` (and `X ≥ 3`), `log X ≤ 2 * log n`.

The per-`n` bound and the uniform one are reconciled not by monotonicity but by *restricting the
range*: splitting off `n < √X`, which contributes at most `√X` to the count and is absorbed into
the constant, leaves `n ≥ √X`, where `log X = 2 log √X ≤ 2 log n`.

This is where the `2 ^ B` in `C_B` comes from. On the remaining range one gets
`s₃(n) ≤ (log X)^B ≤ 2^B (log n)^B`, not `s₃(n) ≤ (log n)^B`, so the constant needed is
`2^(B+1) (C₂+1)`: `2^B` from this bridge and a further `2` from absorbing `s₃ + 1`.
`D_le_of_s3_le` above is stated with the smaller `2 (C₂+1)` because it assumes the *per-`n`*
hypothesis directly, and the assembly supplies the `2^B` itself. -/
theorem log_le_two_mul_log_of_sqrt_le {X : ℝ} {n : ℕ} (hX : 3 ≤ X)
    (hn : Real.sqrt X ≤ (n : ℝ)) :
    Real.log X ≤ 2 * Real.log n := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hsq0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  -- `log √X = log X / 2`.
  have hhalf : Real.log X = 2 * Real.log (Real.sqrt X) := by
    rw [Real.log_sqrt hX0.le]; ring
  rw [hhalf]
  have : Real.log (Real.sqrt X) ≤ Real.log n := Real.log_le_log hsq0 hn
  linarith


/-- **The bridge, contraposed.** On the range `n ≥ √X` (with `n ≥ 3`), an `n` whose `D`-value
exceeds the threshold at `C_B = 2^{B+1}(C₂+1)` has `s₃(n) > (log X)^B` — the *uniform* threshold
that `tail_bound` counts against.

`log_le_two_mul_log_of_sqrt_le` converts the uniform threshold into the per-`n` one at a cost of
`2^B`, and `D_le_of_s3_le` at `K = 2^B` is exactly what pays that cost. -/
theorem log_rpow_lt_s3_of_D_gt (Lit : LiteratureInputs) {C₂ : ℝ}
    (hs2 : ∀ m : ℕ, 1 ≤ m → (s2 m : ℝ) ≤ C₂ * Real.sqrt m)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 3 ≤ X) {n : ℕ} (hn : 3 ≤ n)
    (hsq : Real.sqrt X ≤ (n : ℝ))
    (hD : 2 ^ (B + 1) * (C₂ + 1) * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ B
        < (D n : ℝ)) :
    Real.log X ^ B < (s3 n : ℝ) := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsqrt : ((n : ℝ)) ^ ((1 : ℝ) / 2) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
  rw [hsqrt] at hD
  by_contra hcon
  push Not at hcon
  -- `log X ≤ 2 log n`, so the uniform threshold costs a factor `2^B`.
  have hstep : Real.log X ^ B ≤ 2 ^ B * Real.log n ^ B :=
    calc Real.log X ^ B ≤ (2 * Real.log n) ^ B :=
          Real.rpow_le_rpow hlogX0 (log_le_two_mul_log_of_sqrt_le hX hsq) hB
      _ = 2 ^ B * Real.log n ^ B := Real.mul_rpow (by norm_num) hlogn0
  have h2B : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB
  have hmain := D_le_of_s3_le Lit hs2 hB h2B hn (hcon.trans hstep)
  have hpow : (2 : ℝ) ^ (B + 1) = 2 * 2 ^ B := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  rw [hpow] at hD
  linarith


/-- **The almost-all bound.** Let `B > 5/6`. Then there is `C_B > 0` such that for every `ε > 0`
there is `C_{B,ε} > 0` with

`#{1 ≤ n ≤ X : D(n) > C_B n^{1/2} (log n)^B} ≤ C_{B,ε} X (log X)^{-½(B - 5/6) + ε}`

for every real `X ≥ 3`.

**The quantifier order is the content.** `C_B = 2^{B+1}(C₂+1)` is produced *before* `ε` is
introduced, so `C_B n^{1/2}(log n)^B` is one fixed threshold and the display bounds a single
exceptional set; `C_{B,ε}` comes after `ε` and does depend on it. At the swapped binder order
`density_tendsto_zero` below could not even be stated.

## The four moving parts

1. **`ε` is shrunk first.** `ε₀ = min ε ((B - 5/6)/4)` satisfies `0 < ε₀ < (B - 5/6)/2`, which is
   what `gamma_spec` needs, and the bound at `ε₀` implies the bound at `ε` because `log X ≥ 1`
   makes `(log X) ^ ·` monotone. A large `ε` therefore needs no separate case.

2. **The range split.** `E` is cut at `n = √X`: below it the count is at most `√X + 2` (the `+2`
   covering `n ∈ {1,2}`, which `D_le_of_s3_le` excludes), and above it `log X ≤ 2 log n` converts
   the per-`n` threshold into the uniform `(log X)^B` that `tail_bound` counts — at the cost of the
   `2^B` in `C_B`.

3. **`tail_bound` at `S = ⌊(log X)^B⌋₊`.** `S ≥ 1` for every `X ≥ 3`, and `Nat.floor_lt` turns the
   real inequality `(log X)^B < s₃(n)` into the natural one `S < s₃(n)` with no loss.

4. **Three absorptions, one trade.** The leftovers — `O(1)`, `√X`, and `tail_bound`'s
   `O(S) = O((log X)^B)` — must all be absorbed into `X (log X)^{-a}` with `a > 0`, a term
   *smaller* than `X`. Each is the same trade, `key` below: `v · (log X)^a ≤ w` gives `v ≤ w · u`.
   The three instances are `log_rpow_le_mul_sqrt`, `log_rpow_le_mul` at `a`, and `log_rpow_le_mul`
   at `B + a`. -/
@[zf_tag "thm_almostall"]
theorem exists_almostall_bound (Lit : LiteratureInputs) {B : ℝ} (hB : 5 / 6 < B) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n : ℕ => CB * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ B
            < (D n : ℝ))).card : ℝ)
        ≤ C * X * Real.log X ^ (-(1 / 2 : ℝ) * (B - 5 / 6) + ε) := by
  obtain ⟨C₂, hC₂, hs2⟩ := s2_bound
  have hB0 : (0 : ℝ) ≤ B := by linarith
  refine ⟨2 ^ (B + 1) * (C₂ + 1),
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith), ?_⟩
  intro ε hε
  -- (1) shrink `ε` into `gamma_spec`'s range.
  obtain ⟨ε₀, hε₀, hε₀ε, hε₀B⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ε ∧ ε₀ < (B - 5 / 6) / 2 :=
    ⟨min ε ((B - 5 / 6) / 4), lt_min hε (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  obtain ⟨γ, hγ1, hγ2, hid⟩ := gamma_spec hε₀ hε₀B
  obtain ⟨C₁, hC₁, htail⟩ := tail_bound Lit hγ1 hγ2
  -- `a` is the (positive) decay rate; `-a` is the final exponent at `ε₀`.
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (B - 5 / 6) / 2 - ε₀ := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < B + a := by linarith
  have haa : (0 : ℝ) < a ^ a := Real.rpow_pos_of_pos ha a
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  have hbb : (0 : ℝ) < (B + a) ^ (B + a) := Real.rpow_pos_of_pos hb _
  have h2g : (0 : ℝ) < (2 : ℝ) ^ (γ - 1) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 2 * a ^ a + 2 ^ a * a ^ a
      + C₁ * (B + a) ^ (B + a) + C₁ * 2 ^ (γ - 1) := ⟨_, rfl⟩
  have hCfpos : 0 < Cf := by
    rw [hCfdef]
    have := mul_pos h2a haa
    have := mul_pos hC₁ hbb
    have := mul_pos hC₁ h2g
    linarith
  refine ⟨Cf, hCfpos, ?_⟩
  intro X hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  -- `log X ≥ 1`, i.e. `e ≤ 3`.
  have hLX1 : (1 : ℝ) ≤ Real.log X := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans h3 (Real.log_le_log (by norm_num) hX)
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hLB1 : (1 : ℝ) ≤ Real.log X ^ B := Real.one_le_rpow hLX1 hB0
  have hLB0 : (0 : ℝ) ≤ Real.log X ^ B := by linarith
  -- `u = (log X) ^ (-a)`, the decaying factor at `ε₀`.
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.log X ^ (-(B - 5 / 6) / 2 + ε₀) := ⟨_, rfl⟩
  have hupos : 0 < u := by rw [hudef]; exact Real.rpow_pos_of_pos hLXpos _
  have hau : Real.log X ^ a * u = 1 := by
    rw [hudef, ← Real.rpow_add hLXpos,
      show a + (-(B - 5 / 6) / 2 + ε₀) = (0:ℝ) by rw [hadef]; ring, Real.rpow_zero]
  -- (4) the one trade every absorption is an instance of.
  have key : ∀ v w : ℝ, v * Real.log X ^ a ≤ w → v ≤ w * u := by
    intro v w h
    have h' := mul_le_mul_of_nonneg_right h hupos.le
    rwa [mul_assoc, hau, mul_one] at h'
  -- (3) `S = ⌊(log X)^B⌋₊ ≥ 1`.
  have hS1 : 1 ≤ ⌊Real.log X ^ B⌋₊ := Nat.le_floor (by exact_mod_cast hLB1)
  have hSle : ((⌊Real.log X ^ B⌋₊ : ℕ) : ℝ) ≤ Real.log X ^ B := Nat.floor_le hLB0
  -- (2) the range split.
  obtain ⟨E, hEdef⟩ : ∃ E : Finset ℕ, E = (Finset.Icc 1 ⌊X⌋₊).filter
      (fun n : ℕ => 2 ^ (B + 1) * (C₂ + 1) * (n : ℝ) ^ ((1 : ℝ) / 2)
        * Real.log (n : ℝ) ^ B < (D n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Finset ℕ, G = (Finset.Icc 1 ⌊X⌋₊).filter
      (fun n : ℕ => ⌊Real.log X ^ B⌋₊ < s3 n) := ⟨_, rfl⟩
  rw [← hEdef]
  have hsub : E ⊆ Finset.Icc 1 (⌊Real.sqrt X⌋₊ + 2) ∪ G := by
    rw [hEdef, hGdef]
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnIcc, hnP⟩ := hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
    by_cases hsmall : (n : ℝ) < Real.sqrt X ∨ n ≤ 2
    · refine Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, ?_⟩)
      rcases hsmall with h | h
      · have : n ≤ ⌊Real.sqrt X⌋₊ := Nat.le_floor h.le
        omega
      · omega
    · push Not at hsmall
      obtain ⟨hge, hn3⟩ := hsmall
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnIcc, ?_⟩)
      exact (Nat.floor_lt hLB0).mpr
        (log_rpow_lt_s3_of_D_gt Lit hs2 hB0 hX (by omega) hge hnP)
  have hEN : E.card ≤ (⌊Real.sqrt X⌋₊ + 2) + G.card := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Nat.card_Icc] at h
    omega
  have hER : (E.card : ℝ) ≤ ((⌊Real.sqrt X⌋₊ : ℝ) + 2) + (G.card : ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr hEN
    push_cast at h
    linarith
  have hfloorsq : ((⌊Real.sqrt X⌋₊ : ℕ) : ℝ) ≤ Real.sqrt X :=
    Nat.floor_le (Real.sqrt_nonneg X)
  -- The tail estimate, with the main term folded.
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1))
      * ((⌊Real.log X ^ B⌋₊ : ℕ) : ℝ) ^ (1 - γ) := ⟨_, rfl⟩
  have hG := htail X hX ⌊Real.log X ^ B⌋₊ hS1
  rw [← hGdef, ← hMdef] at hG
  have hmain := main_term_bound (B := B) (γ := γ) (ε := ε₀) (L := Real.log X)
    (X := X) hγ1 hLXpos hLB1 hX0.le hid
  rw [← hMdef, ← hudef] at hmain
  -- The three absorptions.
  have hsqX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hAbs : Real.sqrt X ≤ (2 ^ a * a ^ a * X) * u := by
    refine key _ _ ?_
    calc Real.sqrt X * Real.log X ^ a
        ≤ Real.sqrt X * (2 ^ a * a ^ a * Real.sqrt X) :=
          mul_le_mul_of_nonneg_left (log_rpow_le_mul_sqrt ha hX1) hsq0
      _ = 2 ^ a * a ^ a * (Real.sqrt X * Real.sqrt X) := by ring
      _ = 2 ^ a * a ^ a * X := by rw [hsqX]
  have hOne : (1 : ℝ) ≤ (a ^ a * X) * u := by
    refine key _ _ ?_
    rw [one_mul]
    exact log_rpow_le_mul ha hX1
  have hLog : Real.log X ^ B ≤ ((B + a) ^ (B + a) * X) * u := by
    refine key _ _ ?_
    rw [← Real.rpow_add hLXpos]
    exact log_rpow_le_mul hb hX1
  -- Scale the two tail-estimate summands by `C₁` before combining them.
  have hCS : C₁ * ((⌊Real.log X ^ B⌋₊ : ℕ) : ℝ)
      ≤ C₁ * (((B + a) ^ (B + a) * X) * u) :=
    mul_le_mul_of_nonneg_left (hSle.trans hLog) hC₁.le
  have hCM : C₁ * M ≤ C₁ * (2 ^ (γ - 1) * (X * u)) :=
    mul_le_mul_of_nonneg_left hmain hC₁.le
  have hkey : (E.card : ℝ) ≤ Cf * (X * u) := by
    rw [hCfdef]
    linarith [hER, hfloorsq, hAbs, hOne, hG, hCS, hCM]
  refine hkey.trans ?_
  -- Finally relax `ε₀` back to `ε`: `log X ≥ 1`, so the exponent may only grow.
  have hue : u ≤ Real.log X ^ (-(1 / 2 : ℝ) * (B - 5 / 6) + ε) := by
    rw [hudef]
    exact Real.rpow_le_rpow_of_exponent_le hLX1 (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hue hX0.le) hCfpos.le
  linarith [h]


/-- **"Almost all" in the usual sense**: the exceptional set has density zero.

For `B > 5/6` there is a single `C_B > 0` such that

`#{1 ≤ n ≤ X : D(n) > C_B n^{1/2}(log n)^B} / X → 0` as `X → ∞`.

**This is only possible because `C_B` is bound outside the `∀ ε` in
`exists_almostall_bound`.** With the binders swapped, each `ε` would license its own threshold
`C_{B,ε}`, and there would be no single set whose density one could take.

Taking `ε = (B - 5/6)/4` makes the exponent `-(B - 5/6)/4`, strictly negative, and `log X → ∞` then
sends `(log X) ^ (-(B-5/6)/4) → 0`. Any `0 < ε < ½(B - 5/6)` would do; this one is the
midpoint. -/
theorem density_tendsto_zero (Lit : LiteratureInputs) {B : ℝ} (hB : 5 / 6 < B) :
    ∃ CB : ℝ, 0 < CB ∧
      Tendsto (fun X : ℝ =>
        (((Finset.Icc 1 ⌊X⌋₊).filter
            (fun n : ℕ => CB * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ B
              < (D n : ℝ))).card : ℝ) / X) atTop (nhds 0) := by
  obtain ⟨CB, hCB, hall⟩ := exists_almostall_bound Lit hB
  refine ⟨CB, hCB, ?_⟩
  obtain ⟨C, hC, hbd⟩ := hall ((B - 5 / 6) / 4) (by linarith)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (B - 5 / 6) / 4 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hexp : -(1 / 2 : ℝ) * (B - 5 / 6) + (B - 5 / 6) / 4 = -c := by
    rw [hcdef]; ring
  refine squeeze_zero' (g := fun X : ℝ => C * Real.log X ^ (-c)) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (3:ℝ)] with X hX
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (3:ℝ)] with X hX
    have h := hbd X hX
    rw [hexp] at h
    rw [div_le_iff₀ (by linarith : (0:ℝ) < X)]
    linarith [h]
  · have h1 : Tendsto (fun X : ℝ => Real.log X ^ (-c)) atTop (nhds 0) := by
      have := (tendsto_rpow_neg_atTop hc).comp Real.tendsto_log_atTop
      simpa [Function.comp_def] using this
    simpa using h1.const_mul C

end ZeroFree
