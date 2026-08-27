/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Tactic.NormNum.Prime
public import ZeroFree.Meta.Attr

/-!
# The quadratic character mod `3`, and its local factors

The Legendre symbol `(·/3)` is `1` at integers `≡ 1 mod 3` and `-1` at integers `≡ 2 mod 3`.
Summed over the divisors of a prime power `p^e` it gives `e + 1` when `p ≡ 1 mod 3`, and `1` or
`0` according to the parity of `e` when `p ≡ 2 mod 3`. The divisor sum is the Dirichlet
convolution of the character with `ζ`, hence multiplicative, so for `n` coprime to `3` it is
positive exactly when every prime `≡ 2 mod 3` divides `n` to an even power.

## Main definitions

* `legThree`: the quadratic character mod `3` as an arithmetic function.

## Main results

* `legendreSym_three_eq_one`, `legendreSym_three_eq_neg_one`: the values of the character on the
  two invertible classes mod `3`.
* `sum_legendreSym_three_prime_pow_one`, `sum_legendreSym_three_prime_pow_neg_one`: the local
  factor at a prime `≡ 1 mod 3` and at a prime `≡ 2 mod 3`.
* `sum_divisors_legendreSym_pos_iff`: for `n` coprime to `3`, the divisor sum of the character is
  positive exactly when every prime `≡ 2 mod 3` occurs in `n` to an even power.
-/

@[expose] public section

namespace ZeroFree

open Finset

open scoped ArithmeticFunction

/-- Reduction of a natural number mod `3`, transported into `ZMod 3`. -/
theorem natCast_zmod_three {n r : ℕ} (h : n % 3 = r) :
    (((n : ℤ)) : ZMod 3) = (r : ZMod 3) := by
  have : ((n : ℤ) : ZMod 3) = ((n : ℕ) : ZMod 3) := by push_cast; ring
  rw [this, ← ZMod.natCast_mod n 3, h]

/-- **The character at a prime `≡ 1 mod 3` is `1`.** `1` is a square in
`ZMod 3`. -/
theorem legendreSym_three_eq_one {n : ℕ} (h : n % 3 = 1) :
    legendreSym 3 (n : ℤ) = 1 := by
  have hz : (((n : ℤ)) : ZMod 3) = 1 := by
    rw [natCast_zmod_three h]; norm_num
  refine (legendreSym.eq_one_iff 3 ?_).mpr ?_
  · rw [hz]; decide
  · rw [hz]; decide

/-- **The character at a prime `≡ 2 mod 3` is `-1`.** `2` is the non-residue mod `3`: the squares
are `0` and `1`. -/
theorem legendreSym_three_eq_neg_one {n : ℕ} (h : n % 3 = 2) :
    legendreSym 3 (n : ℤ) = -1 := by
  have hz : (((n : ℤ)) : ZMod 3) = 2 := by
    rw [natCast_zmod_three h]; norm_num
  have hne : (((n : ℤ)) : ZMod 3) ≠ 0 := by rw [hz]; decide
  have hnsq : ¬ IsSquare ((((n : ℤ)) : ZMod 3)) := by rw [hz]; decide
  have hne1 : legendreSym 3 (n : ℤ) ≠ 1 := fun hc =>
    hnsq ((legendreSym.eq_one_iff 3 hne).mp hc)
  have hsq : (legendreSym 3 (n : ℤ)) ^ 2 = 1 := legendreSym.sq_one 3 hne
  have hfac : (legendreSym 3 (n : ℤ) - 1) * (legendreSym 3 (n : ℤ) + 1) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact absurd (by linarith) hne1
  · linarith

/-- The character is `1` at every power of a prime `≡ 1 mod 3`. -/
theorem legendreSym_three_pow_one {p : ℕ} (h1 : p % 3 = 1) (j : ℕ) :
    legendreSym 3 ((p ^ j : ℕ) : ℤ) = 1 := by
  refine legendreSym_three_eq_one ?_
  induction j with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih, h1]

/-- **The local factor at a prime `p ≡ 1 mod 3`** is `e + 1`, hence positive for every
exponent. -/
theorem sum_legendreSym_three_prime_pow_one {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1)
    (e : ℕ) :
    ∑ d ∈ (p ^ e).divisors, legendreSym 3 (d : ℤ) = (e : ℤ) + 1 := by
  rw [Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_congr rfl (fun j _ => legendreSym_three_pow_one h1 j)]
  rw [Finset.sum_const, Finset.card_range]
  ring

/-- The character at a power of a prime `≡ 2 mod 3` alternates: `(-1)^j`. -/
theorem legendreSym_three_pow_neg_one {p : ℕ} (h2 : p % 3 = 2) (j : ℕ) :
    legendreSym 3 ((p ^ j : ℕ) : ℤ) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hcast : ((p ^ (k + 1) : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) * ((p : ℕ) : ℤ) := by
      push_cast; ring
    rw [hcast, legendreSym.mul, ih, legendreSym_three_eq_neg_one h2, pow_succ]

/-- The alternating sum `∑_{j ≤ n} (-1)^j`, which is `1` or `0` according to the parity
of `n`. -/
theorem sum_range_neg_one_pow (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j = if n % 2 = 0 then 1 else 0 := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ((-1 : ℤ)) ^ (k + 1) = -1 := Odd.neg_one_pow (Even.add_one hk)
      have h2 : k % 2 = 0 := Nat.even_iff.mp hk
      rw [if_pos h2, h1, if_neg (by omega)]
      ring
    · have h1 : ((-1 : ℤ)) ^ (k + 1) = 1 := Even.neg_one_pow (Odd.add_one hk)
      have h2 : k % 2 = 1 := Nat.odd_iff.mp hk
      rw [if_neg (by omega), h1, if_pos (by omega)]
      ring

/-- **The local factor at a prime `p ≡ 2 mod 3`** is `1` when the exponent is even and `0` when
it is odd. -/
theorem sum_legendreSym_three_prime_pow_neg_one {p : ℕ} (hp : p.Prime)
    (h2 : p % 3 = 2) (e : ℕ) :
    ∑ d ∈ (p ^ e).divisors, legendreSym 3 (d : ℤ) = if e % 2 = 0 then 1 else 0 := by
  rw [Nat.sum_divisors_prime_pow hp,
    Finset.sum_congr rfl (fun j _ => legendreSym_three_pow_neg_one h2 j),
    sum_range_neg_one_pow]

/-! ### The divisor sum as a multiplicative function

The divisor sum `∑_{d ∣ n} (d/3)` is the Dirichlet convolution of the character with `ζ`, hence
multiplicative, and so factors into the local factors above. -/

/-- The quadratic character mod `3` as an arithmetic function. -/
noncomputable def legThree : ArithmeticFunction ℤ where
  toFun n := legendreSym 3 (n : ℤ)
  map_zero' := by
    simp only [Nat.cast_zero]
    exact (legendreSym.eq_zero_iff 3 0).mpr (by decide)

@[simp] theorem legThree_apply (n : ℕ) : legThree n = legendreSym 3 (n : ℤ) := rfl

/-- The character is multiplicative — in fact completely so, via
`legendreSym.mul`. -/
theorem legThree_isMultiplicative : legThree.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp only [legThree_apply, Nat.cast_mul]
    exact legendreSym.mul 3 m n

/-- The divisor sum of the character, as a value of `legThree * ζ`. -/
theorem sum_divisors_legThree (n : ℕ) :
    ∑ d ∈ n.divisors, legendreSym 3 (d : ℤ)
      = (legThree * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact Finset.sum_congr rfl (fun d _ => (legThree_apply d).symm)

/-- The divisor sum is multiplicative. -/
theorem legThreeZeta_isMultiplicative :
    (legThree * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)).IsMultiplicative :=
  legThree_isMultiplicative.mul
    (ArithmeticFunction.isMultiplicative_zeta.natCast)

/-- The local factor at any prime dividing an `n` coprime to `3` is **nonnegative** — it is
`e + 1`, `1` or `0`. -/
theorem legThreeZeta_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (hp3 : p % 3 ≠ 0)
    (e : ℕ) :
    0 ≤ (legThree * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (p ^ e) := by
  rw [← sum_divisors_legThree]
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h
  · rw [sum_legendreSym_three_prime_pow_one hp h]; positivity
  · rw [sum_legendreSym_three_prime_pow_neg_one hp h]
    split <;> norm_num

/-- The local factor is **positive** exactly when the exponent is even at a prime
`≡ 2 mod 3`, and always positive at a prime `≡ 1 mod 3`. -/
theorem legThreeZeta_prime_pow_pos_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 ≠ 0)
    (e : ℕ) :
    0 < (legThree * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (p ^ e)
      ↔ (p % 3 = 2 → Even e) := by
  rw [← sum_divisors_legThree]
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h
  · rw [sum_legendreSym_three_prime_pow_one hp h, h]
    exact ⟨fun _ hc => absurd hc (by norm_num), fun _ => by positivity⟩
  · rw [sum_legendreSym_three_prime_pow_neg_one hp h, h]
    simp only [forall_const]
    rcases Nat.even_or_odd e with he | he
    · rw [if_pos (Nat.even_iff.mp he)]
      exact ⟨fun _ => he, fun _ => by norm_num⟩
    · rw [if_neg (by have := Nat.odd_iff.mp he; omega)]
      exact ⟨fun hc => absurd hc (by norm_num),
        fun hc => absurd hc (Nat.not_even_iff_odd.mpr he)⟩

/-- For `n` coprime to `3`, the divisor sum of the quadratic character mod `3` is positive exactly
when every prime `≡ 2 mod 3` divides `n` to an even power. -/
theorem sum_divisors_legendreSym_pos_iff {n : ℕ} (hn : n ≠ 0) (h3 : ¬ (3 ∣ n)) :
    0 < ∑ d ∈ n.divisors, legendreSym 3 (d : ℤ)
      ↔ ∀ p : ℕ, p.Prime → p % 3 = 2 → Even (n.factorization p) := by
  classical
  have hfac : ∀ p ∈ n.primeFactors, p % 3 ≠ 0 := by
    intro p hp h0
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have : p = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hpp).mp
      (by omega : (3 : ℕ) ∣ p)).symm
    exact h3 (this ▸ hpn)
  rw [sum_divisors_legThree,
    legThreeZeta_isMultiplicative.multiplicative_factorization _ hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  constructor
  · intro hpos p hp h2
    by_contra hodd
    have hmem : p ∈ n.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hn⟩
      refine Nat.dvd_of_factorization_pos ?_
      intro h0
      rw [h0] at hodd
      exact hodd (by decide)
    have hz : (legThree * (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
        (p ^ n.factorization p) = 0 := by
      rw [← sum_divisors_legThree, sum_legendreSym_three_prime_pow_neg_one hp h2,
        if_neg (by
          rcases Nat.even_or_odd (n.factorization p) with he | he
          · exact absurd he hodd
          · have := Nat.odd_iff.mp he; omega)]
    rw [Finset.prod_eq_zero hmem hz] at hpos
    exact absurd hpos (by norm_num)
  · intro heven
    refine Finset.prod_pos ?_
    intro p hp
    exact (legThreeZeta_prime_pow_pos_iff (Nat.prime_of_mem_primeFactors hp)
      (hfac p hp) _).mpr (fun h2 => heven p (Nat.prime_of_mem_primeFactors hp) h2)

end ZeroFree
