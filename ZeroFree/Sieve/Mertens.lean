/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import ZeroFree.LiteratureInputs
public import ZeroFree.Meta.Attr

/-!
# Mertens' theorem for all primes

`∑_{p ≤ X} 1/p = log log X + O(1)`, obtained from Mertens' theorem in arithmetic progressions by
summing over the residue classes mod `9`. Every prime `p` has `p % 9 ∈ {0, …, 8}`, and
`p % 9 ∈ {0, 3, 6}` forces `3 ∣ p`, hence `p = 3`; since `3 % 9 = 3`, the classes `0` and `6` are
empty and the class `3` contains only `3`. The remaining six classes are the units mod `9`, each
carrying `(1/6) log log X + O(1)`, and `6 · (1/6) = 1`.

## Main results

* `primeRecipSum_eq_sum_classes`: the prime reciprocal sum splits into the nine residue classes
  mod `9`.
* `primeRecipSum_mertens`: `∑_{p ≤ X} 1/p - log log X` is bounded for `X ≥ 3`.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- The primes are partitioned by their residue mod `9`. -/
theorem primeRecipSum_eq_sum_classes (X : ℝ) :
    primeRecipSum X = ∑ a ∈ Finset.range 9, primeRecipSumMod X 9 a := by
  unfold primeRecipSum primeRecipSumMod
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p => p % 9) (t := Finset.range 9)
    (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
    (f := fun p => (1 / (p : ℝ)))]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have ha9 : a % 9 = a := Nat.mod_eq_of_lt (Finset.mem_range.mp ha)
  rw [Finset.filter_filter, ha9]

/-- A prime in a residue class divisible by `3` must be `3`, so those classes
contribute at most `1/3`. -/
theorem primeRecipSumMod_nonunit_le {X : ℝ} {a : ℕ} (ha : a % 3 = 0) :
    primeRecipSumMod X 9 a ≤ 1 / 3 := by
  unfold primeRecipSumMod
  have hsub : (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ p % 9 = a % 9) ⊆ {3} := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨-, hpp, hpa⟩ := hp
    have h3 : 3 ∣ p := by omega
    have : p = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hpp).mp h3).symm
    simp [this]
  calc ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter
        (fun p => Nat.Prime p ∧ p % 9 = a % 9), (1 / (p : ℝ))
      ≤ ∑ p ∈ ({3} : Finset ℕ), (1 / (p : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i _ _; positivity
    _ = 1 / 3 := by norm_num

/-- Each class sum is nonnegative. -/
theorem primeRecipSumMod_nonneg (X : ℝ) (q a : ℕ) : 0 ≤ primeRecipSumMod X q a := by
  unfold primeRecipSumMod
  refine Finset.sum_nonneg ?_
  intro i _; positivity

/-- **Mertens' theorem for all primes**: `∑_{p ≤ X} 1/p = log log X + O(1)`. The six invertible
classes mod `9` each contribute `(1/6) log log X + O(1)`, and the other three classes contribute
at most `1` in total. -/
theorem primeRecipSum_mertens (L : LiteratureInputs) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
      |primeRecipSum X - Real.log (Real.log X)| ≤ K := by
  have hunit : ∀ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ),
      ∃ Ka : ℝ, 0 < Ka ∧ ∀ X : ℝ, 3 ≤ X →
        |primeRecipSumMod X 9 a - (1 / 6 : ℝ) * Real.log (Real.log X)| ≤ Ka := by
    intro a ha
    obtain ⟨Ka, hKa, hbd⟩ := L.mertens (q := 9) (a := a) (by norm_num) (by
      fin_cases ha <;> decide)
    refine ⟨Ka, hKa, fun X hX => ?_⟩
    have htot : ((9 : ℕ).totient : ℝ) = 6 := by
      rw [show (9 : ℕ).totient = 6 by decide]; norm_num
    have := hbd X hX
    rwa [htot] at this
  choose! Kf hKf hKbd using hunit
  have hKsum : 0 ≤ ∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), Kf a :=
    Finset.sum_nonneg (fun a ha => (hKf a ha).le)
  refine ⟨(∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), Kf a) + 1, by linarith, ?_⟩
  intro X hX
  have hsplit : primeRecipSum X
      = (∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), primeRecipSumMod X 9 a)
        + (∑ a ∈ ({0, 3, 6} : Finset ℕ), primeRecipSumMod X 9 a) := by
    rw [primeRecipSum_eq_sum_classes]
    have hsets : (Finset.range 9)
        = ({1, 2, 4, 5, 7, 8} : Finset ℕ) ∪ ({0, 3, 6} : Finset ℕ) := by
      ext a
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    rw [hsets, Finset.sum_union (by decide)]
  have hmain : |(∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), primeRecipSumMod X 9 a)
      - Real.log (Real.log X)| ≤ ∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), Kf a := by
    have hrw : (∑ _a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ),
        (1 / 6 : ℝ) * Real.log (Real.log X)) = Real.log (Real.log X) := by
      rw [Finset.sum_const, show (({1, 2, 4, 5, 7, 8} : Finset ℕ)).card = 6 from by decide]
      ring
    calc |(∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), primeRecipSumMod X 9 a)
            - Real.log (Real.log X)|
        = |∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ),
            (primeRecipSumMod X 9 a - (1 / 6 : ℝ) * Real.log (Real.log X))| := by
          rw [Finset.sum_sub_distrib, hrw]
      _ ≤ ∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ),
            |primeRecipSumMod X 9 a - (1 / 6 : ℝ) * Real.log (Real.log X)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ), Kf a :=
          Finset.sum_le_sum (fun a ha => hKbd a ha X hX)
  have htail : 0 ≤ (∑ a ∈ ({0, 3, 6} : Finset ℕ), primeRecipSumMod X 9 a)
      ∧ (∑ a ∈ ({0, 3, 6} : Finset ℕ), primeRecipSumMod X 9 a) ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg (fun a _ => primeRecipSumMod_nonneg X 9 a)
    · have : ∀ a ∈ ({0, 3, 6} : Finset ℕ), primeRecipSumMod X 9 a ≤ 1 / 3 := by
        intro a ha
        fin_cases ha <;> exact primeRecipSumMod_nonunit_le (by norm_num)
      calc (∑ a ∈ ({0, 3, 6} : Finset ℕ), primeRecipSumMod X 9 a)
          ≤ ∑ _a ∈ ({0, 3, 6} : Finset ℕ), (1 / 3 : ℝ) := Finset.sum_le_sum this
        _ = 1 := by
            rw [Finset.sum_const,
              show (({0, 3, 6} : Finset ℕ)).card = 3 from by decide]
            ring
  rw [hsplit]
  have h1 := abs_le.mp hmain
  rw [abs_le]
  constructor <;> [linarith [htail.1, htail.2, h1.1]; linarith [htail.1, htail.2, h1.2]]

end ZeroFree
