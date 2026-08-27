/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Duro

/-!
# Counting the zero-free columns, and the pointwise bound

A zero-free `μ ⊢ n` has all of its parts in `{1,2,3}`, so it is determined by the triple `(a,b,c)`
of its numbers of parts equal to `3`, `2`, `1`. The relation `3a + 2b + c = n` makes `c` redundant,
so `μ ↦ (a,b)` is injective, and `count_three_le_s3`, `count_two_le_s2` confine `(a,b)` to a box of
`(s₃(n) + 1)(s₂(n) + 1)` pairs. Combined with `s₃(n) ≪ n^{1/4}` and `s₂(n) ≪ n^{1/2}` this gives
the pointwise bound `D(n) ≪ n^{3/4}`.

## Main results

* `D_le_succ_s3_mul_succ_s2`: `D n ≤ (s₃ n + 1)(s₂ n + 1)` for `n ≥ 3`.
* `exists_pointwise_bound`: there is a single `C > 0` with `D n ≤ C n^{3/4}` for every `n ≥ 1`.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-! ### A multiset with all parts in `{1,2,3}` is determined by two of its counts -/

/-- The sum of a multiset all of whose elements lie in `{1,2,3}`, read off its
three counts: `3a + 2b + c`. -/
private theorem sum_eq_of_forall_mem_three :
    ∀ m : Multiset ℕ, (∀ x ∈ m, x = 1 ∨ x = 2 ∨ x = 3) →
      m.sum = 3 * m.count 3 + 2 * m.count 2 + m.count 1 := by
  intro m
  induction m using Multiset.induction_on with
  | empty => intro _; simp
  | cons a m ih =>
    intro hm
    have ha : a = 1 ∨ a = 2 ∨ a = 3 := hm a (Multiset.mem_cons_self a m)
    have hrest := ih fun x hx => hm x (Multiset.mem_cons_of_mem hx)
    rcases ha with rfl | rfl | rfl <;>
      simp only [Multiset.sum_cons, Multiset.count_cons] <;> norm_num <;> omega

/-- **Dropping the count of `1`s is harmless.** Two partitions of `n` with all
parts in `{1,2,3}` and the same numbers of parts equal to `3` and to `2` are
equal: the sum condition forces the numbers of parts equal to `1` to agree too,
and no other count is nonzero. -/
private theorem partition_eq_of_count_eq {n : ℕ} {μ ν : Nat.Partition n}
    (hμ : ∀ x ∈ μ.parts, x = 1 ∨ x = 2 ∨ x = 3)
    (hν : ∀ x ∈ ν.parts, x = 1 ∨ x = 2 ∨ x = 3)
    (h3 : μ.parts.count 3 = ν.parts.count 3)
    (h2 : μ.parts.count 2 = ν.parts.count 2) :
    μ = ν := by
  have hsμ := sum_eq_of_forall_mem_three μ.parts hμ
  have hsν := sum_eq_of_forall_mem_three ν.parts hν
  rw [μ.parts_sum] at hsμ
  rw [ν.parts_sum] at hsν
  have h1 : μ.parts.count 1 = ν.parts.count 1 := by omega
  refine Nat.Partition.ext (Multiset.ext.mpr fun a => ?_)
  by_cases ha : a = 1 ∨ a = 2 ∨ a = 3
  · rcases ha with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  · rw [Multiset.count_eq_zero.mpr fun h => ha (hμ a h),
      Multiset.count_eq_zero.mpr fun h => ha (hν a h)]

/-! ### The counting step -/

/-- **The counting step.** For `n ≥ 3`, `D(n) ≤ (s₃(n) + 1)(s₂(n) + 1)`.

The map `μ ↦ (#parts equal to 3, #parts equal to 2)` sends the zero-free partitions of `n` into
`range (s₃(n)+1) ×ˢ range (s₂(n)+1)`: it lands there by `count_three_le_s3` and `count_two_le_s2`,
and it is injective by `partition_eq_of_count_eq`. Only the first half of
`parts_mem_and_count_two_even` is used — that every part lies in `{1,2,3}` — since the parity of
the number of parts equal to `2` plays no role in the size of the box. -/
@[zf_tag "lem_count_D"]
theorem D_le_succ_s3_mul_succ_s2 (L : LiteratureInputs) {n : ℕ} (hn : 3 ≤ n) :
    D n ≤ (s3 n + 1) * (s2 n + 1) := by
  -- The filter defining `D` is classical: the zero-free condition is not decidable.
  classical
  have hn1 : 1 ≤ n := by omega
  have key : D n ≤ (Finset.range (s3 n + 1) ×ˢ Finset.range (s2 n + 1)).card := by
    rw [D]
    refine Finset.card_le_card_of_injOn
      (fun μ : Nat.Partition n => (μ.parts.count 3, μ.parts.count 2)) ?_ ?_
    · intro μ hmem
      rw [Finset.mem_coe, Finset.mem_filter] at hmem
      rw [Finset.mem_coe, Finset.mem_product]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (count_three_le_s3 L hn1 μ hmem.2)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (count_two_le_s2 hn1 μ hmem.2))⟩
    · intro μ hμ ν hν heq
      rw [Finset.mem_coe, Finset.mem_filter] at hμ hν
      exact partition_eq_of_count_eq (parts_mem_and_count_two_even L hn μ hμ.2).1
        (parts_mem_and_count_two_even L hn ν hν.2).1
        (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  simpa using key

/-! ### The pointwise bound -/

/-- **The pointwise bound** `D(n) ≪ n^{3/4}`, with the implied constant made explicit: there is a
single `C > 0`, quantified outside `n`, with `D(n) ≤ C n^{3/4}` for every `n ≥ 1`. The exponent is
`Real.rpow`, matching `s2_bound` and `s3_bound`.

For `n ≥ 3` this is `D_le_succ_s3_mul_succ_s2` composed with `s₃(n) ≤ C₃ n^{1/4}` and
`s₂(n) ≤ C₂ n^{1/2}`, using `1 ≤ n^{1/4}` and `1 ≤ n^{1/2}` to absorb the two `+1`s into the
constants, and `Real.rpow_add` to multiply the two powers. The values `n = 1, 2` are absorbed into
`C`, which carries `D 1` and `D 2` as summands, so neither is ever computed. -/
@[zf_tag "thm_pointwise"]
theorem exists_pointwise_bound (L : LiteratureInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (D n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨C3, hC3, hs3⟩ := s3_bound
  obtain ⟨C2, hC2, hs2⟩ := s2_bound
  have hD1 : (0 : ℝ) ≤ (D 1 : ℝ) := Nat.cast_nonneg _
  have hD2 : (0 : ℝ) ≤ (D 2 : ℝ) := Nat.cast_nonneg _
  have hbase : (0 : ℝ) < (C3 + 1) * (C2 + 1) := by nlinarith
  refine ⟨(C3 + 1) * (C2 + 1) + (D 1 : ℝ) + (D 2 : ℝ), by linarith, ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 3 with hlt | h3
  · -- `n = 1` or `n = 2`: the constant already dominates `D n`, and `n^{3/4} ≥ 1`.
    have hn12 : n = 1 ∨ n = 2 := by omega
    rcases hn12 with rfl | rfl
    · rw [Nat.cast_one, Real.one_rpow, mul_one]
      linarith
    · have hx : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      nlinarith
  · -- `n ≥ 3`: the counting step, then the two core-distance bounds.
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
    have h4 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hnR1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hnR1 (by norm_num)
    have hDR : (D n : ℝ) ≤ ((s3 n : ℝ) + 1) * ((s2 n : ℝ) + 1) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (D_le_succ_s3_mul_succ_s2 L h3)
      push_cast at h
      linarith
    have hb3 : (s3 n : ℝ) + 1 ≤ (C3 + 1) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have h := hs3 n hn
      have hring : (C3 + 1) * (n : ℝ) ^ ((1 : ℝ) / 4)
          = C3 * (n : ℝ) ^ ((1 : ℝ) / 4) + (n : ℝ) ^ ((1 : ℝ) / 4) := by ring
      rw [hring]; linarith
    have hb2 : (s2 n : ℝ) + 1 ≤ (C2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have h := hs2 n hn
      rw [Real.sqrt_eq_rpow] at h
      have hring : (C2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 2)
          = C2 * (n : ℝ) ^ ((1 : ℝ) / 2) + (n : ℝ) ^ ((1 : ℝ) / 2) := by ring
      rw [hring]; linarith
    have hprod : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 2)
        = (n : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add hnR0]; norm_num
    have hcast0 : (0 : ℝ) ≤ (s2 n : ℝ) + 1 := by positivity
    have hb30 : (0 : ℝ) ≤ (C3 + 1) * (n : ℝ) ^ ((1 : ℝ) / 4) :=
      le_of_lt (mul_pos (by linarith) (by linarith))
    have hrpow0 : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hnR0) _
    calc (D n : ℝ)
        ≤ ((s3 n : ℝ) + 1) * ((s2 n : ℝ) + 1) := hDR
      _ ≤ ((C3 + 1) * (n : ℝ) ^ ((1 : ℝ) / 4)) * ((C2 + 1) * (n : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul hb3 hb2 hcast0 hb30
      _ = ((C3 + 1) * (C2 + 1)) * (n : ℝ) ^ ((3 : ℝ) / 4) := by rw [← hprod]; ring
      _ ≤ ((C3 + 1) * (C2 + 1) + (D 1 : ℝ) + (D 2 : ℝ)) * (n : ℝ) ^ ((3 : ℝ) / 4) := by
          apply mul_le_mul_of_nonneg_right _ hrpow0
          linarith

end ZeroFree
