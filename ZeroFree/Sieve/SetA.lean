/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import ZeroFree.LiteratureInputs
public import ZeroFree.Sieve.Mertens
public import ZeroFree.Meta.Attr

/-!
# Consequences of membership in the sieve set

Every element of `𝓐` is Loeschian and congruent to `1` mod `9`, and every element of
`𝓑_r = r · 𝓐` is congruent to `r` mod `9`, and is Loeschian when `r ∈ {1,4,7}`. On the analytic
side, the primes of `𝓐` are exactly the primes `≡ 1 mod 9`, which carry a `1/6` share of the
prime reciprocal sum: so `𝓐` satisfies the sieve hypothesis of the Matomäki–Radziwiłł gap theorem
with `α = 1/7`, and its sieve density has exact order `(log X)^{-5/6}`. Together these bound the
`γ`-th moment of the gaps between consecutive elements of `𝓐`, and of `𝓑_r`, by
`O(X (log X)^{5(γ-1)/6})` for `1 ≤ γ < 3/2`.

## Main results

* `mem_setA_loeschian`, `mem_setB_loeschian`: elements of `𝓐`, and of `𝓑_r` for `r ∈ {1,4,7}`,
  are Loeschian.
* `mem_setA_mod_nine`, `mem_setB_mod_nine`: elements of `𝓐` are `≡ 1 mod 9`, and elements of
  `𝓑_r` are `≡ r mod 9`.
* `setA_sieve`: `𝓐` satisfies the sieve hypothesis of the gap theorem with `α = 1/7`.
* `sieveDensity_setA`: `δ(𝓐; X)` has exact order `(log X)^{-5/6}`.
* `setA_gaps`, `setB_gaps`: the `γ`-th gap moments of `𝓐` and of `𝓑_r`.
-/

@[expose] public section

namespace ZeroFree

/-- Every element of `𝓐` is Loeschian.

A prime `p ≡ 2 mod 3` cannot be `≡ 1 mod 9`, so `𝓐`'s defining condition gives `6 ∣ v_p(m)`,
hence `v_p(m)` is even — exactly what the Eisenstein criterion asks for. -/
@[zf_tag "lem_A_loeschian"]
theorem mem_setA_loeschian (L : LiteratureInputs) {m : ℕ} (hm : m ∈ SetA) :
    Loeschian m := by
  obtain ⟨h1, _, hexp⟩ := hm
  refine (L.eisenstein h1).mpr ?_
  intro p hp hp3
  have hp9 : p % 9 ≠ 1 := by omega
  exact (even_iff_two_dvd).mpr (dvd_trans (by norm_num) (hexp p hp hp9))

/-- Every element of `𝓑_r` is Loeschian, for `r ∈ {1,4,7}`.

The dilation factor is Loeschian, the `𝓐`-part is Loeschian by `mem_setA_loeschian`, and
`Loeschian.mul` composes them — the whole content is that `x² + xy + y²` is a norm form. -/
@[zf_tag "lem_B_loeschian"]
theorem mem_setB_loeschian (L : LiteratureInputs) {r m : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) (hm : m ∈ SetB r) : Loeschian m := by
  obtain ⟨a, haA, rfl⟩ := hm
  have hrL : Loeschian r := by
    rcases hr with rfl | rfl | rfl
    · exact loeschian_one
    · exact loeschian_four
    · exact loeschian_seven
  exact hrL.mul (mem_setA_loeschian L haA)

/-! ### Congruence mod `9`

Two prime-power facts, then a multiplicative induction. -/

/-- A prime power with `p ≡ 1 mod 9` is itself `≡ 1 mod 9`. -/
theorem pow_modEq_one_of_mod_nine {p e : ℕ} (hp : p % 9 = 1) :
    p ^ e ≡ 1 [MOD 9] := by
  have h1 : p ≡ 1 [MOD 9] := by unfold Nat.ModEq; omega
  calc p ^ e ≡ 1 ^ e [MOD 9] := h1.pow e
    _ = 1 := one_pow e

/-- A prime power `p ^ e` with `p ≠ 3` and `6 ∣ e` is `≡ 1 mod 9`.

Euler's theorem at `n = 9`: the unit group mod `9` has order `φ(9) = 6`, so `p ^ 6 ≡ 1` for every
`p` coprime to `9`, and a prime `p ≠ 3` is coprime to `9 = 3²`. -/
theorem pow_modEq_one_of_six_dvd {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (he : 6 ∣ e) : p ^ e ≡ 1 [MOD 9] := by
  have hcop : Nat.Coprime p 9 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
      (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨k, rfl⟩ := he
  have h6 : p ^ 6 ≡ 1 [MOD 9] := by
    have h := Nat.ModEq.pow_totient hcop
    rwa [show Nat.totient 9 = 6 by decide] at h
  calc p ^ (6 * k) = (p ^ 6) ^ k := by rw [pow_mul]
    _ ≡ 1 ^ k [MOD 9] := h6.pow k
    _ = 1 := one_pow k

/-- Every prime power dividing an element of `𝓐` is `≡ 1 mod 9`. The case split is exactly `𝓐`'s
definition: either the prime is `≡ 1 mod 9`, or its exponent is divisible by `6`. The prime `3`
cannot occur, since `¬ 3 ∣ m`. -/
theorem primePow_modEq_one {m : ℕ} (hm : m ∈ SetA) {p : ℕ} (hp : p.Prime) :
    p ^ (m.factorization p) ≡ 1 [MOD 9] := by
  obtain ⟨h1, h3, hexp⟩ := hm
  by_cases h9 : p % 9 = 1
  · exact pow_modEq_one_of_mod_nine h9
  · by_cases hp3 : p = 3
    · subst hp3
      rw [Nat.factorization_eq_zero_of_not_dvd h3, pow_zero]
    · exact pow_modEq_one_of_six_dvd hp hp3 (hexp p hp h9)

/-- Every element of `𝓐` is `≡ 1 mod 9`.

The multiplicative induction: `m` is the product of its prime powers, and each of those is
`≡ 1 mod 9` by `primePow_modEq_one`, so the product is too. -/
@[zf_tag "lem_A_mod_nine"]
theorem mem_setA_mod_nine {m : ℕ} (hm : m ∈ SetA) : m % 9 = 1 := by
  have hm0 : m ≠ 0 := by have := hm.1; omega
  have hcast : ((m : ℕ) : ZMod 9) = 1 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Finsupp.prod, Nat.cast_prod]
    refine Finset.prod_eq_one ?_
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors
      (by simpa [Nat.support_factorization] using hpmem)
    have h := primePow_modEq_one hm hp
    have hz : ((p ^ m.factorization p : ℕ) : ZMod 9) = ((1 : ℕ) : ZMod 9) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    simpa using hz
  have : (m : ZMod 9) = ((1 : ℕ) : ZMod 9) := by simpa using hcast
  have := (ZMod.natCast_eq_natCast_iff m 1 9).mp this
  simpa [Nat.ModEq] using this

/-- Every element of `𝓑_r` is `≡ r mod 9`, for every `r`: the dilation argument is indifferent to
which `r` it is. -/
@[zf_tag "lem_B_mod_nine"]
theorem mem_setB_mod_nine {r m : ℕ} (hm : m ∈ SetB r) : m ≡ r [MOD 9] := by
  obtain ⟨a, haA, rfl⟩ := hm
  have ha : a ≡ 1 [MOD 9] := by
    have := mem_setA_mod_nine haA
    unfold Nat.ModEq; omega
  calc r * a ≡ r * 1 [MOD 9] := ha.mul_left r
    _ = r := mul_one r

/-! ### Feeding Mertens into the gap theorem

Two steps: identify the `𝓐`-restricted prime sum with the residue-class sum, at the level of
`Finset` filters, and then read off the sieve hypothesis from the uniform form of Mertens'
theorem in arithmetic progressions at `q = 9`, `a = 1`, where `φ(9) = 6`. -/

/-- The `𝓐`-restricted prime sum *is* the sum over primes `≡ 1 mod 9`. -/
theorem primeRecipSumMem_setA (X : ℝ) :
    primeRecipSumMem X SetA = primeRecipSumMod X 9 1 := by
  classical
  unfold primeRecipSumMem primeRecipSumMod
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr ?_
  intro x _
  constructor
  · rintro ⟨hp, hA⟩
    exact ⟨hp, by simpa using (prime_mem_setA_iff hp).mp hA⟩
  · rintro ⟨hp, h9⟩
    exact ⟨hp, (prime_mem_setA_iff hp).mpr (by simpa using h9)⟩

/-- Prefix sums of prime reciprocals are monotone, so the tail sum is nonnegative. -/
theorem primeRecipSum_mono {w z : ℝ} (h : w ≤ z) :
    primeRecipSum w ≤ primeRecipSum z := by
  unfold primeRecipSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · have hfl : ⌊w⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor h
    apply Finset.filter_subset_filter
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro i _ _
    positivity

/-- `𝓐` satisfies the sieve hypothesis of the gap theorem, with `α = 1/7`.

The uniform Mertens estimate at `q = 9`, `a = 1` puts the sum over primes `≡ 1 mod 9` within
`1/6` of its expected share, and `1/6 ≥ 1/7` with the tail sum nonnegative. The slack is
deliberate: any `α < 1/6` would do, and a strict inequality is what the gap theorem wants. -/
@[zf_tag "lem_A_sieve"]
theorem setA_sieve (L : LiteratureInputs) :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (1 / 7 : ℝ) * primeRecipSumIoc w z - K / Real.log w
        ≤ primeRecipSumMemIoc w z SetA := by
  obtain ⟨K, hK, hmert⟩ := L.mertensUniform (q := 9) (a := 1) (by norm_num)
    (by decide)
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz
  have htot : ((9 : ℕ).totient : ℝ) = 6 := by
    rw [show (9 : ℕ).totient = 6 by decide]; norm_num
  have hbound := hmert w z hw hwz
  rw [htot] at hbound
  have hEq : primeRecipSumMemIoc w z SetA = primeRecipSumModIoc w z 9 1 := by
    unfold primeRecipSumMemIoc primeRecipSumModIoc
    rw [primeRecipSumMem_setA, primeRecipSumMem_setA]
  have hP : 0 ≤ primeRecipSumIoc w z := by
    unfold primeRecipSumIoc
    have := primeRecipSum_mono hwz
    linarith
  rw [hEq]
  have habs := abs_le.mp hbound
  linarith [habs.1, habs.2, hP]

/-! ### The sieve density of `𝓐`

In four movements. The product defining `δ(𝓐; X)` becomes a sum of logarithms; each
`log (1 - 1/p)` is sandwiched between `-1/p - 2/p²` and `-1/p`, so the accumulated error is
bounded by the convergent `∑ 1/p²`; the resulting `∑_{p ≤ X, p ≢ 1 (9)} 1/p` is
`(5/6) log log X + O(1)`, by subtracting Mertens for the class `1 mod 9` from Mertens for all
primes; and exponentiating turns the two-sided `O(1)` into the two constants. -/

/-- `-1/x - 2/x² ≤ log (1 - 1/x) ≤ -1/x` for every real `x ≥ 2`.

Both halves are `log t ≤ t - 1`: directly at `t = 1 - 1/x` for the upper bound, and at
`t = x/(x-1)`, whose logarithm is `-log (1 - 1/x)`, for the lower — there `x/(x-1) - 1 = 1/(x-1)`,
and `1/(x-1) ≤ 1/x + 2/x²` holds exactly because `x ≥ 2`. -/
private theorem log_one_sub_one_div_bounds {x : ℝ} (hx : 2 ≤ x) :
    -(1 / x) - 2 / x ^ 2 ≤ Real.log (1 - 1 / x) ∧
      Real.log (1 - 1 / x) ≤ -(1 / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hx1 : (0 : ℝ) < x - 1 := by linarith
  have hx1' : x - 1 ≠ 0 := ne_of_gt hx1
  have hinv : 1 / x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
  have hy : (0 : ℝ) < 1 - 1 / x := by linarith
  refine ⟨?_, by linarith [Real.log_le_sub_one_of_pos hy]⟩
  have hdiv : (1 : ℝ) - 1 / x = (x - 1) / x := by field_simp
  have hneg : Real.log ((x - 1) / x) = -Real.log (x / (x - 1)) := by
    rw [← Real.log_inv, inv_div]
  have hle : Real.log (x / (x - 1)) ≤ x / (x - 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hx0 hx1)
  have hid : 1 / x + 2 / x ^ 2 - (x / (x - 1) - 1)
      = (x - 2) / (x ^ 2 * (x - 1)) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (x - 2) / (x ^ 2 * (x - 1)) :=
    div_nonneg (by linarith) (mul_nonneg (sq_nonneg x) (by linarith))
  rw [hdiv, hneg]
  linarith

/-- `∑_{p ∈ s} 2/p² ≤ 2` whenever `s` is a finite set of naturals in `[2, M)`. This bounds the
total second-order error in `log_one_sub_one_div_bounds`, and a tail of `∑_n 1/n²` is all that is
needed for it. -/
private theorem sum_two_div_sq_le {M : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range M) (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∑ p ∈ s, 2 / (p : ℝ) ^ 2 ≤ 2 := by
  have hsub : s ⊆ Finset.Ioo 1 M := fun p hp =>
    Finset.mem_Ioo.mpr ⟨by have := h2 p hp; omega, Finset.mem_range.mp (hs hp)⟩
  have hstep : ∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ p ∈ Finset.Ioo 1 M, ((p : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  have hIoo : ∑ p ∈ Finset.Ioo 1 M, ((p : ℝ) ^ 2)⁻¹ ≤ 1 :=
    calc ∑ p ∈ Finset.Ioo 1 M, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / (((1 : ℕ) : ℝ) + 1) :=
          sum_Ioo_inv_sq_le 1 M
      _ = 1 := by norm_num
  have hrw : ∑ p ∈ s, 2 / (p : ℝ) ^ 2 = 2 * ∑ p ∈ s, ((p : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [div_eq_mul_inv]
  rw [hrw]
  linarith

/-- The logarithm of a product `∏ (1 - 1/p)` over naturals in `[2, M)` is the negated reciprocal
sum, up to an absolute error of `2`. -/
private theorem abs_log_prod_one_sub_add_sum_le {M : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range M) (h2 : ∀ p ∈ s, 2 ≤ p) :
    |Real.log (∏ p ∈ s, (1 - 1 / (p : ℝ))) + ∑ p ∈ s, (1 / (p : ℝ))| ≤ 2 := by
  have hcast : ∀ p ∈ s, (2 : ℝ) ≤ (p : ℝ) := fun p hp => by exact_mod_cast h2 p hp
  have hpos : ∀ p ∈ s, (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    intro p hp
    have h := hcast p hp
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h
    linarith
  rw [Real.log_prod fun p hp => (hpos p hp).ne']
  have hupper : ∑ p ∈ s, Real.log (1 - 1 / (p : ℝ)) ≤ ∑ p ∈ s, -(1 / (p : ℝ)) :=
    Finset.sum_le_sum fun p hp => (log_one_sub_one_div_bounds (hcast p hp)).2
  have hlower : ∑ p ∈ s, (-(1 / (p : ℝ)) - 2 / (p : ℝ) ^ 2)
      ≤ ∑ p ∈ s, Real.log (1 - 1 / (p : ℝ)) :=
    Finset.sum_le_sum fun p hp => (log_one_sub_one_div_bounds (hcast p hp)).1
  have e1 : ∑ p ∈ s, -(1 / (p : ℝ)) = -∑ p ∈ s, (1 / (p : ℝ)) := by simp
  have e2 : ∑ p ∈ s, (-(1 / (p : ℝ)) - 2 / (p : ℝ) ^ 2)
      = -(∑ p ∈ s, (1 / (p : ℝ))) - ∑ p ∈ s, 2 / (p : ℝ) ^ 2 := by
    rw [Finset.sum_sub_distrib, e1]
  rw [e1] at hupper
  rw [e2] at hlower
  have hsq := sum_two_div_sq_le hs h2
  rw [abs_le]
  constructor <;> linarith

open scoped Classical in
/-- The primes `≤ X` split into those lying in `𝓐` and those outside it; by `prime_mem_setA_iff`
the first group is exactly the residue class `1 mod 9`, and the second is the index set of
`sieveDensity SetA X`. -/
theorem primeRecipSum_eq_add_notMem_setA (X : ℝ) :
    primeRecipSum X = primeRecipSumMod X 9 1
      + ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∉ SetA),
          (1 / (p : ℝ)) := by
  rw [← primeRecipSumMem_setA]
  unfold primeRecipSum primeRecipSumMem
  rw [← Finset.sum_filter_add_sum_filter_not
      ((Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p))
      (fun p => p ∈ SetA) (fun p => (1 / (p : ℝ))),
    Finset.filter_filter, Finset.filter_filter]

/-- The sieve density of `𝓐` has exact order `(log X)^(-5/6)`: there are constants `c₁, c₂ > 0`
with `c₁ (log X)^(-5/6) ≤ δ(𝓐; X) ≤ c₂ (log X)^(-5/6)` for every `X ≥ 3`.

`prime_mem_setA_iff` identifies the index set of the product as the primes `p ≢ 1 mod 9`. Its
logarithm is `-∑_{p ≤ X, p ≢ 1 (9)} 1/p` up to an absolute constant, and Mertens for all primes
minus Mertens for the class `1 mod 9` — where `φ(9) = 6`, so that class carries
`(1/6) log log X` — evaluates that sum as `(5/6) log log X + O(1)`. Exponentiating converts the
two-sided `O(1)` into `c₁` and `c₂`; both are generous, being exponentials of the sum of the two
Mertens constants and the error `2`. -/
@[zf_tag "lem_A_delta"]
theorem sieveDensity_setA (L : LiteratureInputs) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ X : ℝ, 3 ≤ X →
      c₁ * Real.log X ^ (-(5 : ℝ) / 6) ≤ sieveDensity SetA X ∧
        sieveDensity SetA X ≤ c₂ * Real.log X ^ (-(5 : ℝ) / 6) := by
  classical
  obtain ⟨K, -, hall⟩ := primeRecipSum_mertens L
  obtain ⟨K', -, hone⟩ := L.mertens (q := 9) (a := 1) (by norm_num) (by decide)
  refine ⟨Real.exp (-(K + K' + 2)), Real.exp (K + K' + 2), Real.exp_pos _,
    Real.exp_pos _, ?_⟩
  intro X hX
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have h2 : ∀ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ p ∉ SetA), 2 ≤ p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1.two_le
  have hδ : sieveDensity SetA X
      = ∏ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∉ SetA),
          (1 - 1 / (p : ℝ)) := rfl
  have hδpos : 0 < sieveDensity SetA X := by
    rw [hδ]
    refine Finset.prod_pos fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2 p hp
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hprod : |Real.log (sieveDensity SetA X)
      + ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∉ SetA),
          (1 / (p : ℝ))| ≤ 2 := by
    rw [hδ]
    exact abs_log_prod_one_sub_add_sum_le (Finset.filter_subset _ _) h2
  have htot : ((9 : ℕ).totient : ℝ) = 6 := by
    rw [show (9 : ℕ).totient = 6 by decide]; norm_num
  have honeX := hone X hX
  rw [htot] at honeX
  have hA := abs_le.mp (hall X hX)
  have hB := abs_le.mp honeX
  have hC := abs_le.mp hprod
  have hsplit := primeRecipSum_eq_add_notMem_setA X
  have hkey : |Real.log (sieveDensity SetA X) + 5 / 6 * Real.log (Real.log X)|
      ≤ K + K' + 2 := by
    rw [abs_le]
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]
  have hk := abs_le.mp hkey
  have hrpow : Real.log X ^ (-(5 : ℝ) / 6)
      = Real.exp (Real.log (Real.log X) * (-(5 : ℝ) / 6)) :=
    Real.rpow_def_of_pos hlogX _
  refine ⟨?_, ?_⟩
  · calc Real.exp (-(K + K' + 2)) * Real.log X ^ (-(5 : ℝ) / 6)
        = Real.exp (-(K + K' + 2) + Real.log (Real.log X) * (-(5 : ℝ) / 6)) := by
          rw [hrpow, ← Real.exp_add]
      _ ≤ Real.exp (Real.log (sieveDensity SetA X)) :=
          Real.exp_le_exp.mpr (by linarith [hk.1])
      _ = sieveDensity SetA X := Real.exp_log hδpos
  · calc sieveDensity SetA X = Real.exp (Real.log (sieveDensity SetA X)) :=
          (Real.exp_log hδpos).symm
      _ ≤ Real.exp (K + K' + 2 + Real.log (Real.log X) * (-(5 : ℝ) / 6)) :=
          Real.exp_le_exp.mpr (by linarith [hk.2])
      _ = Real.exp (K + K' + 2) * Real.log X ^ (-(5 : ℝ) / 6) := by
          rw [hrpow, ← Real.exp_add]


/-! ### Gap moments

The density lower bound converts into a bound on the `γ`-th moment of the gaps between
consecutive elements of `SetA`. All the analytic content is in the Matomäki–Radziwiłł gap
theorem; what is shown here is that `SetA` satisfies its hypotheses and that the density bound
feeds through the exponent correctly. -/

/-- For `1 ≤ γ < 3/2`, the `γ`-th moment of the gaps between consecutive elements of `SetA` up to
`X` is `O(X (log X) ^ (5/6 · (γ - 1)))`.

The gap theorem gives the moment bound in terms of the sieve density,
`C₀ * X * sieveDensity SetA X ^ (1 - γ)`, once `isMultiplicativeSet_setA` and `setA_sieve` supply
its hypotheses at `α = 1/7`. Then, because `1 - γ ≤ 0`, the map `u ↦ u ^ (1 - γ)` is *antitone* on
the positive reals — so the *lower* bound half of `sieveDensity_setA` is what bounds the density
from above after raising to `1 - γ`:

`sieveDensity SetA X ^ (1-γ) ≤ (c₁ * log X ^ (-5/6)) ^ (1-γ)
                             = c₁ ^ (1-γ) * log X ^ (5/6 · (γ-1))`.

The direction matters: the density is *small*, since it decays in `log X`, and a small base
raised to a negative power is *large*, which is why a lower bound on the density is the useful
half here. -/
@[zf_tag "lem_A_gaps"]
theorem setA_gaps (L : LiteratureInputs) {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (· ∈ SetA) i : ℝ) ≤ X),
        ((Nat.nth (· ∈ SetA) (i + 1) - Nat.nth (· ∈ SetA) i : ℝ)) ^ γ
      ≤ C * X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by
  obtain ⟨K, hK, hsieve⟩ := setA_sieve L
  obtain ⟨C₀, hC₀, hgap⟩ :=
    L.gapTheorem isMultiplicativeSet_setA (α := 1 / 7) (by norm_num) hK hsieve hγ1 hγ2
  obtain ⟨c₁, c₂, hc₁, hc₂, hdens⟩ := sieveDensity_setA L
  have hexp : 1 - γ ≤ 0 := by linarith
  refine ⟨C₀ * c₁ ^ (1 - γ), by positivity, ?_⟩
  intro X hX
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlow : c₁ * Real.log X ^ (-(5 : ℝ) / 6) ≤ sieveDensity SetA X := (hdens X hX).1
  have hbase : 0 < c₁ * Real.log X ^ (-(5 : ℝ) / 6) := by positivity
  have hpow : sieveDensity SetA X ^ (1 - γ)
      ≤ (c₁ * Real.log X ^ (-(5 : ℝ) / 6)) ^ (1 - γ) :=
    Real.rpow_le_rpow_of_nonpos hbase hlow hexp
  have hsplit : (c₁ * Real.log X ^ (-(5 : ℝ) / 6)) ^ (1 - γ)
      = c₁ ^ (1 - γ) * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by
    rw [Real.mul_rpow hc₁.le (Real.rpow_nonneg hlogpos.le _),
      ← Real.rpow_mul hlogpos.le]
    congr 1
    ring_nf
  have hXpos : (0 : ℝ) < X := by linarith
  calc ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (· ∈ SetA) i : ℝ) ≤ X),
        ((Nat.nth (· ∈ SetA) (i + 1) - Nat.nth (· ∈ SetA) i : ℝ)) ^ γ
      ≤ C₀ * X * sieveDensity SetA X ^ (1 - γ) := hgap X hX
    _ ≤ C₀ * X * ((c₁ * Real.log X ^ (-(5 : ℝ) / 6)) ^ (1 - γ)) := by
        have : (0 : ℝ) ≤ C₀ * X := by positivity
        nlinarith [hpow, this]
    _ = C₀ * c₁ ^ (1 - γ) * X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by
        rw [hsplit]; ring


/-! ### Gap moments for the dilated sets

`SetB r` is `r · SetA`, so its gap moments are `r ^ γ` times those of `SetA` on a rescaled range.
Making that precise needs one structural fact — that `Nat.nth` commutes with the dilation — and
that in turn needs `SetA` to be infinite, since `Nat.nth` of a finite predicate is not the
enumeration one expects past the end. -/

/-- `SetA` is infinite: it contains every power of `19`.

`19 % 9 = 1`, so the defining condition is vacuous at `19`, the only prime with a positive
exponent in `19 ^ k`, and `3 ∤ 19 ^ k`. Any prime `≡ 1 mod 9` would do; `19` is the smallest. -/
theorem setA_infinite : SetA.Infinite := by
  have hmem : ∀ k : ℕ, 19 ^ k ∈ SetA := by
    intro k
    refine ⟨Nat.one_le_pow _ _ (by norm_num), ?_, ?_⟩
    · intro hdvd
      have h3 : Nat.Prime 3 := by norm_num
      have := (Nat.Prime.dvd_of_dvd_pow h3 hdvd)
      omega
    · intro q hq hq9
      have hne : q ≠ 19 := by intro h; rw [h] at hq9; omega
      have h19 : Nat.Prime 19 := by norm_num
      have hz : (Nat.factorization 19) q = 0 := by
        rw [h19.factorization, Finsupp.single_apply]
        simp [Ne.symm hne]
      rw [Nat.factorization_pow]
      simp [hz]
  have hinj : Function.Injective (fun k : ℕ => 19 ^ k) :=
    fun a b hab => Nat.pow_right_injective (by norm_num) hab
  exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 19 ^ k) hinj hmem

/-- Membership in `SetB r` at a dilated point, for `r ≥ 1`. -/
theorem mem_setB_mul_iff {r : ℕ} (hr : 1 ≤ r) (a : ℕ) :
    r * a ∈ SetB r ↔ a ∈ SetA := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have hab' : a = b := Nat.eq_of_mul_eq_mul_left hr hab
    rw [hab']
    exact hb
  · intro ha; exact ⟨a, ha, rfl⟩


/-- `SetB r` is infinite too, for `r ≥ 1`, being a dilation of `SetA`. -/
theorem setB_infinite {r : ℕ} (hr : 1 ≤ r) : (SetB r).Infinite := by
  apply Set.Infinite.mono (s := (fun a => r * a) '' SetA)
  · rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · exact setA_infinite.image (Set.injOn_of_injective
      (fun x y hxy => Nat.eq_of_mul_eq_mul_left hr hxy))

/-- **`Nat.nth` commutes with the dilation.** The `i`-th element of `SetB r` is `r` times the
`i`-th element of `SetA`.

The elements of `SetB r` below `r * a` are exactly `r * b` for `b ∈ SetA` with `b < a`, so the
filtered range on one side is the literal image of the other under `b ↦ r * b`, which is injective
for `r ≥ 1`. `Nat.count` therefore agrees at dilated points, and `Nat.nth_count` transports that
to the enumerations; infinitude of `SetA` is what licenses `Nat.count_nth_of_infinite`. -/
theorem nth_setB {r : ℕ} (hr : 1 ≤ r) (i : ℕ) :
    Nat.nth (· ∈ SetB r) i = r * Nat.nth (· ∈ SetA) i := by
  classical
  have hrpos : 0 < r := hr
  have hcount : ∀ a : ℕ, Nat.count (· ∈ SetB r) (r * a) = Nat.count (· ∈ SetA) a := by
    intro a
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    have himg : (Finset.range (r * a)).filter (fun m => m ∈ SetB r)
        = ((Finset.range a).filter (fun b => b ∈ SetA)).image (fun b => r * b) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hlt, b, hb, rfl⟩
        exact ⟨b, ⟨lt_of_mul_lt_mul_left hlt (Nat.zero_le r), hb⟩, rfl⟩
      · rintro ⟨b, ⟨hba, hb⟩, rfl⟩
        exact ⟨mul_lt_mul_of_pos_left hba hrpos, b, hb, rfl⟩
    rw [himg, Finset.card_image_of_injective _
      (fun x y hxy => Nat.eq_of_mul_eq_mul_left hrpos hxy)]
  have hinf : {n : ℕ | n ∈ SetA}.Infinite := setA_infinite
  set a := Nat.nth (fun x => x ∈ SetA) i with ha
  have hamem : a ∈ SetA :=
    Nat.nth_mem_of_infinite (p := fun x => x ∈ SetA) hinf i
  have hca : Nat.count (fun x => x ∈ SetA) a = i := by
    rw [ha]; exact Nat.count_nth_of_infinite (p := fun x => x ∈ SetA) hinf i
  have hbmem : r * a ∈ SetB r := (mem_setB_mul_iff hr a).mpr hamem
  have : Nat.count (· ∈ SetB r) (r * a) = i := by rw [hcount a, hca]
  calc Nat.nth (· ∈ SetB r) i
      = Nat.nth (· ∈ SetB r) (Nat.count (· ∈ SetB r) (r * a)) := by rw [this]
    _ = r * a := Nat.nth_count hbmem


/-- The gap moments for `SetB r`, `r ∈ {1,4,7}`, match those of `SetA` up to a constant.

`nth_setB` turns each gap `b_{i+1} - b_i` into `r (a_{i+1} - a_i)`, pulling a factor `r ^ γ` out
of the sum, and turns the condition `b_i ≤ X` into `a_i ≤ X / r`. Applying `setA_gaps` at `X / r`
then gives the bound, and since `log (X / r) ≤ log X` and the exponent `5/6 (γ - 1)` is
nonnegative for `γ ≥ 1`, the `log` factor can be relaxed back to `log X`.

The small-`X` range is folded into the constant: if `X / r < 3` then `X < 21`, where only finitely
many indices contribute. -/
@[zf_tag "lem_B_gaps"]
theorem setB_gaps (L : LiteratureInputs) {r : ℕ} (hr : r = 1 ∨ r = 4 ∨ r = 7)
    {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ X),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ
      ≤ C * X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by
  classical
  have hr1 : 1 ≤ r := by rcases hr with rfl | rfl | rfl <;> omega
  obtain ⟨C₁, hC₁, hA⟩ := setA_gaps L hγ1 hγ2
  have hAinf : (Set.ofPred (fun x => x ∈ SetA)).Infinite := setA_infinite
  refine ⟨(r : ℝ) ^ γ * C₁, by positivity, ?_⟩
  intro X hX
  have hterm : ∀ i : ℕ,
      ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
          - Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ
        = (r : ℝ) ^ γ * ((Nat.nth (fun x => x ∈ SetA) (i + 1)
            - Nat.nth (fun x => x ∈ SetA) i : ℝ)) ^ γ := by
    intro i
    have hmono : Nat.nth (fun x => x ∈ SetA) i ≤ Nat.nth (fun x => x ∈ SetA) (i + 1) :=
      Nat.nth_monotone hAinf (by omega)
    have hdiff : (0 : ℝ) ≤ (Nat.nth (fun x => x ∈ SetA) (i + 1) : ℝ)
        - (Nat.nth (fun x => x ∈ SetA) i : ℝ) := by
      have : ((Nat.nth (fun x => x ∈ SetA) i : ℕ) : ℝ)
          ≤ ((Nat.nth (fun x => x ∈ SetA) (i + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hmono
      linarith
    rw [nth_setB hr1, nth_setB hr1]
    push_cast
    rw [show (r : ℝ) * (Nat.nth (fun x => x ∈ SetA) (i + 1) : ℝ)
          - (r : ℝ) * (Nat.nth (fun x => x ∈ SetA) i : ℝ)
        = (r : ℝ) * ((Nat.nth (fun x => x ∈ SetA) (i + 1) : ℝ)
            - (Nat.nth (fun x => x ∈ SetA) i : ℝ)) by ring]
    exact Real.mul_rpow (by positivity) hdiff
  have hsub : (Finset.range (⌊X⌋₊ + 1)).filter
        (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ X)
      ⊆ (Finset.range (⌊X⌋₊ + 1)).filter
        (fun i => (Nat.nth (fun x => x ∈ SetA) i : ℝ) ≤ X) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have := hi.2
    rw [nth_setB hr1] at this
    push_cast at this
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.nth (fun x => x ∈ SetA) i)]
  calc ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ X),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ
      = ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ X),
          (r : ℝ) ^ γ * ((Nat.nth (fun x => x ∈ SetA) (i + 1)
              - Nat.nth (fun x => x ∈ SetA) i : ℝ)) ^ γ :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = (r : ℝ) ^ γ * ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ X),
          ((Nat.nth (fun x => x ∈ SetA) (i + 1)
              - Nat.nth (fun x => x ∈ SetA) i : ℝ)) ^ γ := by
        rw [Finset.mul_sum]
    _ ≤ (r : ℝ) ^ γ * ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetA) i : ℝ) ≤ X),
          ((Nat.nth (fun x => x ∈ SetA) (i + 1)
              - Nat.nth (fun x => x ∈ SetA) i : ℝ)) ^ γ := by
        have hrγ : (0 : ℝ) ≤ (r : ℝ) ^ γ := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hrγ
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i _ _
        exact Real.rpow_nonneg (by
          have hmono : Nat.nth (fun x => x ∈ SetA) i
              ≤ Nat.nth (fun x => x ∈ SetA) (i + 1) :=
            Nat.nth_monotone hAinf (by omega)
          have : ((Nat.nth (fun x => x ∈ SetA) i : ℕ) : ℝ)
              ≤ ((Nat.nth (fun x => x ∈ SetA) (i + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hmono
          linarith) _
    _ ≤ (r : ℝ) ^ γ * (C₁ * X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1))) := by
        have hrγ : (0 : ℝ) ≤ (r : ℝ) ^ γ := by positivity
        exact mul_le_mul_of_nonneg_left (hA X hX) hrγ
    _ = (r : ℝ) ^ γ * C₁ * X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by ring

end ZeroFree
