/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.NormNum.Prime
public import ZeroFree.Meta.Attr

/-!
# The sieve vocabulary for the almost-all bound

A set of positive integers is *multiplicative* when membership in it is determined by coprime
factorisations, and its *sieve density* is `δ(N; X) = ∏_{p ≤ X, p ∉ N} (1 - 1/p)`. The set `𝓐`
of positive integers free of the factor `3` in which every prime `p ≢ 1 mod 9` occurs to an
exponent divisible by `6` is such a set, and the primes it contains are exactly the primes
`≡ 1 mod 9`.

## Main definitions

* `IsMultiplicativeSet`: membership in a set of positive integers is determined by coprime
  factorisations in both directions.
* `sieveDensity`: the product `∏_{p ≤ X, p ∉ N} (1 - 1/p)`.
* `SetA`: the multiplicative set `𝓐`.
* `SetB`: the dilations `𝓑_r = r · 𝓐`.

## Main results

* `isMultiplicativeSet_setA`: `𝓐` is multiplicative.
* `prime_mem_setA_iff`: a prime belongs to `𝓐` exactly when it is `≡ 1 mod 9`.
-/

@[expose] public section

namespace ZeroFree


/-- A set of positive integers is *multiplicative* when membership in it is determined by coprime
factorisations in both directions. -/
@[zf_tag "def_multiplicative"]
def IsMultiplicativeSet (N : Set ℕ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → (m * n ∈ N ↔ m ∈ N ∧ n ∈ N)

open scoped Classical in
/-- The sieve density `δ(N; X) = ∏_{p ≤ X, p ∉ N} (1 - 1/p)`. -/
@[zf_tag "def_delta"]
noncomputable def sieveDensity (N : Set ℕ) (X : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∉ N),
    (1 - 1 / (p : ℝ))

/-- The multiplicative set `𝓐`: no factor of `3`, and every prime not congruent to `1` mod `9`
occurring to an exponent divisible by `6`. The prime `3` needs the separate condition `¬ 3 ∣ m`
because `3 % 9 = 3 ≠ 1`, so the exponent condition alone would only force `6 ∣ v_3(m)` rather
than `v_3(m) = 0`. -/
@[zf_tag "def_A"]
def SetA : Set ℕ :=
  {m | 1 ≤ m ∧ ¬ (3 ∣ m) ∧ ∀ p : ℕ, p.Prime → p % 9 ≠ 1 → 6 ∣ m.factorization p}

/-- The shifted sets `𝓑_r = r · 𝓐`, the dilations of `𝓐` by a factor `r`. -/
@[zf_tag "def_B"]
def SetB (r : ℕ) : Set ℕ := {m | ∃ a ∈ SetA, m = r * a}

/-- For coprime `m` and `n`, no prime has a positive exponent in both. -/
private theorem factorization_eq_zero_of_coprime {m n : ℕ} (h : Nat.Coprime m n)
    {p : ℕ} (hp : p.Prime) :
    m.factorization p = 0 ∨ n.factorization p = 0 := by
  by_contra hc
  push Not at hc
  have h1 : p ∣ m := Nat.dvd_of_factorization_pos hc.1
  have h2 : p ∣ n := Nat.dvd_of_factorization_pos hc.2
  have : p ∣ 1 := by
    have hg := Nat.dvd_gcd h1 h2
    rwa [Nat.Coprime.gcd_eq_one h] at hg
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- `𝓐` is multiplicative. -/
@[zf_tag "lem_A_mult"]
theorem isMultiplicativeSet_setA : IsMultiplicativeSet SetA := by
  intro m n hm hn hcop
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  have hfac : (m * n).factorization = m.factorization + n.factorization :=
    Nat.factorization_mul hm0 hn0
  have h3 : (3 ∣ m * n) ↔ (3 ∣ m ∨ 3 ∣ n) :=
    Nat.Prime.dvd_mul (by norm_num)
  constructor
  · rintro ⟨-, h3mn, hexp⟩
    refine ⟨⟨hm, fun hd => h3mn (h3.mpr (Or.inl hd)), ?_⟩,
            ⟨hn, fun hd => h3mn (h3.mpr (Or.inr hd)), ?_⟩⟩
    · intro p hp hpne
      have h6 := hexp p hp hpne
      rw [hfac] at h6
      simp only [Finsupp.add_apply] at h6
      rcases factorization_eq_zero_of_coprime hcop hp with hz | hz
      · rw [hz]; exact dvd_zero 6
      · omega
    · intro p hp hpne
      have h6 := hexp p hp hpne
      rw [hfac] at h6
      simp only [Finsupp.add_apply] at h6
      rcases factorization_eq_zero_of_coprime hcop hp with hz | hz
      · omega
      · rw [hz]; exact dvd_zero 6
  · rintro ⟨⟨-, h3m, hm6⟩, ⟨-, h3n, hn6⟩⟩
    refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm0 hn0), ?_, ?_⟩
    · intro hd
      rcases h3.mp hd with hd' | hd'
      · exact h3m hd'
      · exact h3n hd'
    · intro p hp hpne
      rw [hfac]
      simp only [Finsupp.add_apply]
      exact Nat.dvd_add (hm6 p hp hpne) (hn6 p hp hpne)

/-- The primes in `𝓐` are exactly the primes congruent to `1` mod `9`. -/
@[zf_tag "lem_A_primes"]
theorem prime_mem_setA_iff {p : ℕ} (hp : p.Prime) : p ∈ SetA ↔ p % 9 = 1 := by
  have hfac : p.factorization = Finsupp.single p 1 := hp.factorization
  constructor
  · intro hmem
    by_contra hne
    have h6 : 6 ∣ p.factorization p := hmem.2.2 p hp hne
    rw [hfac, Finsupp.single_eq_same] at h6
    omega
  · intro h9
    have h3 : ¬ (3 ∣ p) := by
      intro hdvd
      obtain ⟨k, hk⟩ := hdvd
      omega
    refine ⟨hp.one_lt.le.trans' (by omega), h3, ?_⟩
    intro q hq hqne
    have hqp : q ≠ p := by rintro rfl; exact hqne h9
    have hz : p.factorization q = 0 := by
      rw [hfac]; exact Finsupp.single_eq_of_ne hqp
    rw [hz]
    exact dvd_zero 6

end ZeroFree
