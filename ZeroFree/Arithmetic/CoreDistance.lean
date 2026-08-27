/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.NormNum
public import ZeroFree.Arithmetic.Basic
public import ZeroFree.Arithmetic.Interval
public import ZeroFree.Meta.Attr

/-!
# The two core distances

The `2`-core distance `s₂(n)` is the least shift `s` for which `n - 2s` is triangular, and the
`3`-core distance `s₃(n)` is the least shift `s` for which `3(n - 3s) + 1` is Loeschian. Both are
taken as the infimum of a set of admissible shifts, which is total in `ℕ` and returns `0` on the
empty set; that default is never reached, because `s = n/2` leaves `0 = T_0` or `1 = T_1`
according to the parity of `n`, and `s = n/3` leaves a residue `m < 3` with `3m + 1 ∈ {1, 4, 7}`
Loeschian. The two distances satisfy `s₂(n) ≤ 6√n` and `s₃(n) ≤ 40 n^{1/4}`.

## Main definitions

* `shifts2`, `shifts3`: the sets of admissible `2`- and `3`-shifts of `n`.
* `s2`, `s3`: the `2`- and `3`-core distances, the least admissible shifts.

## Main results

* `s2_mem`, `s3_mem`: the least admissible shift is admissible, so the default branch of each
  definition is never taken.
* `s2_bound`: `s₂(n) ≤ 6√n` for every `n ≥ 1`.
* `s3_bound`: `s₃(n) ≤ 40 n^{1/4}` for every `n ≥ 1`.
-/

@[expose] public section

namespace ZeroFree

/-- The set of admissible `2`-shifts: those `s` with `n - 2s` triangular. -/
def shifts2 (n : ℕ) : Set ℕ := {s | 2 * s ≤ n ∧ ∃ u : ℕ, n - 2 * s = tri u}

/-- The set of admissible `3`-shifts: those `s` with `3(n - 3s) + 1` Loeschian. -/
def shifts3 (n : ℕ) : Set ℕ := {s | 3 * s ≤ n ∧ Loeschian (3 * (n - 3 * s) + 1)}

/-- The `2`-core distance `s₂(n)`: the least shift `s` for which `n - 2s` is triangular, and `0`
if there is none. `s2_mem` shows the default branch is never taken. -/
@[zf_tag "def_s2"]
noncomputable def s2 (n : ℕ) : ℕ := sInf (shifts2 n)

/-- The `3`-core distance `s₃(n)`: the least shift `s` for which `3(n - 3s) + 1` is Loeschian,
and `0` if there is none. `s3_mem` shows the default branch is never taken. -/
@[zf_tag "def_s3"]
noncomputable def s3 (n : ℕ) : ℕ := sInf (shifts3 n)

theorem tri_zero : tri 0 = 0 := by simp [tri]

theorem tri_one : tri 1 = 1 := by simp [tri]

/-- Halving `n` is an admissible `2`-shift: it leaves `0` or `1` according to parity, and both
are triangular. -/
theorem div_two_mem_shifts2 (n : ℕ) : n / 2 ∈ shifts2 n := by
  refine ⟨by omega, ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    exact ⟨0, by rw [tri_zero]; omega⟩
  · obtain ⟨k, hk⟩ := ho
    exact ⟨1, by rw [tri_one]; omega⟩

/-- Dividing `n` by `3` is an admissible `3`-shift: it leaves a residue `m < 3`, and `3m + 1` is
Loeschian. -/
theorem div_three_mem_shifts3 (n : ℕ) : n / 3 ∈ shifts3 n :=
  ⟨by omega, loeschian_three_mul_add_one_of_lt_three (by omega)⟩

theorem shifts2_nonempty (n : ℕ) : (shifts2 n).Nonempty :=
  ⟨n / 2, div_two_mem_shifts2 n⟩

theorem shifts3_nonempty (n : ℕ) : (shifts3 n).Nonempty :=
  ⟨n / 3, div_three_mem_shifts3 n⟩

/-- The `2`-core distance is attained: `2 s₂(n) ≤ n` and `n - 2 s₂(n)` is triangular.
Equivalently, the default branch of `s2` is never taken. -/
@[zf_tag "lem_s2_mem"]
theorem s2_mem (n : ℕ) : 2 * s2 n ≤ n ∧ ∃ u : ℕ, n - 2 * s2 n = tri u :=
  Nat.sInf_mem (shifts2_nonempty n)

/-- The `3`-core distance is attained: `3 s₃(n) ≤ n` and `3(n - 3 s₃(n)) + 1` is Loeschian.
Equivalently, the default branch of `s3` is never taken. -/
@[zf_tag "lem_s3_mem"]
theorem s3_mem (n : ℕ) : 3 * s3 n ≤ n ∧ Loeschian (3 * (n - 3 * s3 n) + 1) :=
  Nat.sInf_mem (shifts3_nonempty n)

/-- The crude bound `s₂(n) ≤ n / 2`. -/
theorem s2_le (n : ℕ) : s2 n ≤ n / 2 := Nat.sInf_le (div_two_mem_shifts2 n)

/-- The crude bound `s₃(n) ≤ n / 3`. -/
theorem s3_le (n : ℕ) : s3 n ≤ n / 3 := Nat.sInf_le (div_three_mem_shifts3 n)

/-! ### The `2`-core distance is `O(√n)`

Put `u = ⌊√(2n)⌋`. Then `T_{u-1} ≤ n` always, with `n - T_{u-1} ≤ 2u`, so a single `Nat.sqrt`
supplies the base triangular number with no maximality argument. For parity only one alternative
is ever needed: `T_{u-1} - T_{u-3}` is `2u - 3`, which is odd, so exactly one of `n - T_{u-1}` and
`n - T_{u-3}` is even. -/

/-- The shift built from `T_{u-1}` or `T_{u-3}`, whichever has the right parity, is admissible;
hence `s₂(n) ≤ 2⌊√(2n)⌋`. -/
theorem s2_le_two_mul_sqrt {n : ℕ} (hn : 5 ≤ n) :
    s2 n ≤ 2 * Nat.sqrt (2 * n) := by
  have hle : Nat.sqrt (2 * n) * Nat.sqrt (2 * n) ≤ 2 * n := Nat.sqrt_le (2 * n)
  have hlt : 2 * n < (Nat.sqrt (2 * n) + 1) * (Nat.sqrt (2 * n) + 1) :=
    Nat.lt_succ_sqrt (2 * n)
  have hu3 : 3 ≤ Nat.sqrt (2 * n) := by
    by_contra h
    have h2 : Nat.sqrt (2 * n) + 1 ≤ 3 := by omega
    nlinarith [hlt, h2]
  obtain ⟨v, hv⟩ : ∃ v, Nat.sqrt (2 * n) = v + 3 := ⟨Nat.sqrt (2 * n) - 3, by omega⟩
  rw [hv] at hle hlt ⊢
  obtain ⟨w, hw⟩ : ∃ w, w = v * v := ⟨v * v, rfl⟩
  have hle' : w + 6 * v + 9 ≤ 2 * n := by rw [hw]; nlinarith [hle]
  have hlt' : 2 * n < w + 8 * v + 16 := by rw [hw]; nlinarith [hlt]
  have h2A : 2 * tri (v + 2) = w + 5 * v + 6 := by
    rw [two_mul_tri, hw]; ring
  have h2B : 2 * tri v = w + v := by rw [two_mul_tri, hw]; ring
  rcases Nat.even_or_odd (n - tri (v + 2)) with hev | hod
  · obtain ⟨k, hk⟩ := hev
    have hmem : k ∈ shifts2 n := ⟨by omega, v + 2, by omega⟩
    exact le_trans (Nat.sInf_le hmem) (by omega)
  · obtain ⟨k, hk⟩ := hod
    obtain ⟨j, hj⟩ : ∃ j, n - tri v = 2 * j := ⟨(n - tri v) / 2, by omega⟩
    have hmem : j ∈ shifts2 n := ⟨by omega, v, by omega⟩
    exact le_trans (Nat.sInf_le hmem) (by omega)

/-- `s₂(n) ≤ 6√n` for every `n ≥ 1`.

Not sharp: `s2_le_two_mul_sqrt` gives `2⌊√(2n)⌋ < 2√2·√n < 3√n`. The constant `6` absorbs that
slack and the finitely many `n < 5` where the argument needs `⌊√(2n)⌋ ≥ 3`. -/
@[zf_tag "lem_s2_bound"]
theorem s2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (s2 n : ℝ) ≤ C * Real.sqrt n := by
  refine ⟨6, by norm_num, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsn0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hn1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hsn, hsn0]
  by_cases h5 : 5 ≤ n
  · have hs : s2 n ≤ 2 * Nat.sqrt (2 * n) := s2_le_two_mul_sqrt h5
    have hq : Nat.sqrt (2 * n) * Nat.sqrt (2 * n) ≤ 2 * n := Nat.sqrt_le (2 * n)
    have hqR : ((Nat.sqrt (2 * n) : ℝ)) ^ 2 ≤ 2 * (n : ℝ) := by
      have : ((Nat.sqrt (2 * n) * Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) :=
        Nat.cast_le.mpr hq
      push_cast at this
      nlinarith [this]
    have hq0 : (0 : ℝ) ≤ (Nat.sqrt (2 * n) : ℝ) := Nat.cast_nonneg _
    have hqle : ((Nat.sqrt (2 * n) : ℝ)) ≤ 2 * Real.sqrt (n : ℝ) := by
      nlinarith [hqR, hsn, hsn0, hq0]
    have hsR : (s2 n : ℝ) ≤ 2 * (Nat.sqrt (2 * n) : ℝ) := by
      have : ((s2 n : ℕ) : ℝ) ≤ ((2 * Nat.sqrt (2 * n) : ℕ) : ℝ) := Nat.cast_le.mpr hs
      push_cast at this
      linarith [this]
    nlinarith [hsR, hqle, hsn0]
  · have hcrude : s2 n ≤ 2 := by have := s2_le n; omega
    have : (s2 n : ℝ) ≤ 2 := by exact_mod_cast hcrude
    nlinarith [hn1, this]

/-! ### The `3`-core distance is `O(n^{1/4})`

The bound splits into a discrete half, which manufactures an admissible shift out of an integer
`A` in a prescribed class mod `9` together with an overshooting `T`, and an analytic half, which
shows that `T = ⌊N^{1/4}⌋` overshoots. -/

/-- **A square root of `N` modulo `9`, when `N ≡ 1 mod 3`.** Then `N % 9 ∈ {1, 4, 7}`, and each of
those is a square mod `9`: `1² = 1`, `2² = 4`, `4² = 16 ≡ 7`. -/
theorem exists_sq_mod_nine {N : ℕ} (h : N % 3 = 1) :
    ∃ r ∈ ({1, 2, 4} : Finset ℕ), r ^ 2 % 9 = N % 9 := by
  have h9 : N % 9 = 1 ∨ N % 9 = 4 ∨ N % 9 = 7 := by omega
  rcases h9 with h9 | h9 | h9
  · exact ⟨1, by decide, by rw [h9]; norm_num⟩
  · exact ⟨2, by decide, by rw [h9]; norm_num⟩
  · exact ⟨4, by decide, by rw [h9]; norm_num⟩

/-- **Nine consecutive integers meet every class mod `9`**: for all `n` and `r` there is an `A`
with `n ≤ A ≤ n + 8` and `A ≡ r mod 9`. -/
theorem exists_mem_Icc_mod_nine (n r : ℕ) :
    ∃ A, n ≤ A ∧ A ≤ n + 8 ∧ A % 9 = r % 9 :=
  ⟨n + (r % 9 + 9 - n % 9) % 9, by omega, by omega, by omega⟩

/-- **The discrete half of the `3`-core distance bound.**

With `N = 3n+1`, suppose some `T` already *overshoots*: `A² + 27T² > N` for the `A` the argument
is about to build. Then `s₃(n) ≤ 6T + 2`.

The hypothesis is stated with `⌊√N⌋ - 8` in place of `A`, the weakest form the analytic half
`lt_sq_add_floor_fourth_root` supplies: every admissible `A` is at least `⌊√N⌋ - 8`, so
`(⌊√N⌋ - 8)² ≤ A²` and the overshoot transfers.

`exists_sq_mod_nine` gives `r` with `r² ≡ N` mod `9`, and `exists_mem_Icc_mod_nine` puts an
`A ≡ r` mod `9` into `[⌊√N⌋-8, ⌊√N⌋]`, so `A² ≤ N` and `A² ≡ N` mod `9`. Taking
`y = ⌊√((N - A²)/27)⌋` makes `A² + 27y² ≤ N < A² + 27(y+1)²`, and the overshoot hypothesis forces
`y ≤ T`. The deficit `N - A² - 27y²` is then divisible by `9` and smaller than `27(2y+1)`, so the
shift `s = (N - A² - 27y²)/9` is at most `6T + 2` and lies in `shifts3 n`:
`3(n - 3s) + 1 = A² + 27y²`, which is Loeschian by `sq_add_twentySeven_mul_sq`. -/
theorem s3_le_of_lt_sq_add {n T : ℕ} (hn : 27 ≤ n)
    (hT : 3 * n + 1 < (Nat.sqrt (3 * n + 1) - 8) ^ 2 + 27 * T ^ 2) :
    s3 n ≤ 6 * T + 2 := by
  have h81 : (9 : ℕ) ^ 2 ≤ 3 * n + 1 := by
    have h : (9 : ℕ) ^ 2 = 81 := by norm_num
    omega
  have hS9 : 9 ≤ Nat.sqrt (3 * n + 1) := Nat.le_sqrt'.mpr h81
  obtain ⟨r, -, hr2⟩ := exists_sq_mod_nine (N := 3 * n + 1) (by omega)
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_mem_Icc_mod_nine (Nat.sqrt (3 * n + 1) - 8) r
  have hAle : A ≤ Nat.sqrt (3 * n + 1) := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = A ^ 2 := ⟨_, rfl⟩
  have haN : a ≤ 3 * n + 1 := by rw [ha]; exact Nat.le_sqrt'.mp hAle
  have ha1 : 1 ≤ a := by rw [ha]; exact Nat.one_le_pow 2 A (by omega)
  have hamod : a % 9 = (3 * n + 1) % 9 := by
    rw [ha, Nat.pow_mod, hA3, ← Nat.pow_mod]; exact hr2
  have hsub : (Nat.sqrt (3 * n + 1) - 8) ^ 2 ≤ a := by
    rw [ha]; exact Nat.pow_le_pow_left hA1 2
  have hTa : 3 * n + 1 < a + 27 * T ^ 2 := by omega
  -- `y` is the largest natural number with `27 y² ≤ N - a`.
  obtain ⟨y, hy⟩ : ∃ y, y = Nat.sqrt ((3 * n + 1 - a) / 27) := ⟨_, rfl⟩
  have hy1 : y * y ≤ (3 * n + 1 - a) / 27 := by rw [hy]; exact Nat.sqrt_le _
  have hy2 : (3 * n + 1 - a) / 27 < (y + 1) * (y + 1) := by
    rw [hy]; exact Nat.lt_succ_sqrt _
  obtain ⟨b, hb⟩ : ∃ b, b = y * y := ⟨_, rfl⟩
  have hbsq : y ^ 2 = b := by rw [hb]; ring
  have hb2 : (y + 1) * (y + 1) = b + 2 * y + 1 := by rw [hb]; ring
  rw [← hb] at hy1
  rw [hb2] at hy2
  have hkey1 : a + 27 * b ≤ 3 * n + 1 := by omega
  have hkey2 : 3 * n + 1 < a + 27 * (b + 2 * y + 1) := by omega
  obtain ⟨c, hc⟩ : ∃ c, c = T * T := ⟨_, rfl⟩
  have hcsq : T ^ 2 = c := by rw [hc]; ring
  rw [hcsq] at hTa
  have hyT : y ≤ T := by
    by_contra hcon
    have h1 : T * T ≤ y * y := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨s, hsdef⟩ : ∃ s, 9 * s = 3 * n + 1 - a - 27 * b :=
    ⟨(3 * n + 1 - a - 27 * b) / 9, by omega⟩
  have hsn : 3 * s ≤ n := by omega
  have hsT : s ≤ 6 * T + 2 := by omega
  have hval : 3 * (n - 3 * s) + 1 = A ^ 2 + 27 * y ^ 2 := by
    rw [← ha, hbsq]; omega
  have hL : Loeschian (A ^ 2 + 27 * y ^ 2) := by
    refine ⟨by omega, (A : ℤ) - 3 * (y : ℤ), 6 * (y : ℤ), ?_⟩
    push_cast
    ring
  have hmem : s ∈ shifts3 n := ⟨hsn, by rw [hval]; exact hL⟩
  exact le_trans (Nat.sInf_le hmem) hsT

/-- **The analytic half of the `3`-core distance bound.**

`T = ⌊N^{1/4}⌋` overshoots, where `N = 3n+1`: `(⌊√N⌋ - 8)² + 27T² > N`.

This is `interval_length` transported to the integers. That lemma gives `N - 27T² < (√N - 9)²`,
and `√N < ⌊√N⌋ + 1` makes `0 ≤ √N - 9 < ⌊√N⌋ - 8`, so the square on the right only grows when
`√N - 9` is replaced by `⌊√N⌋ - 8`. -/
theorem lt_sq_add_floor_fourth_root {n : ℕ} (hn : 27 ≤ n) :
    3 * n + 1 < (Nat.sqrt (3 * n + 1) - 8) ^ 2 +
      27 * ⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ ^ 2 := by
  have h81 : (9 : ℕ) ^ 2 ≤ 3 * n + 1 := by
    have h : (9 : ℕ) ^ 2 = 81 := by norm_num
    omega
  have hS9 : 9 ≤ Nat.sqrt (3 * n + 1) := Nat.le_sqrt'.mpr h81
  have hNR : (81 : ℝ) ≤ ((3 * n + 1 : ℕ) : ℝ) := by
    have h : (81 : ℕ) ≤ 3 * n + 1 := by omega
    exact_mod_cast h
  have hkey := interval_length (N := ((3 * n + 1 : ℕ) : ℝ)) hNR
  have hsqrt9 : (9 : ℝ) ≤ Real.sqrt ((3 * n + 1 : ℕ) : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith [hNR])
  have hpos : (0 : ℝ) < (Nat.sqrt (3 * n + 1) : ℝ) + 1 := by positivity
  have hsqrtlt : Real.sqrt ((3 * n + 1 : ℕ) : ℝ) < (Nat.sqrt (3 * n + 1) : ℝ) + 1 := by
    rw [Real.sqrt_lt' hpos]
    have hlt : 3 * n + 1 < (Nat.sqrt (3 * n + 1) + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hltR : ((3 * n + 1 : ℕ) : ℝ) < (((Nat.sqrt (3 * n + 1) + 1) ^ 2 : ℕ) : ℝ) :=
      Nat.cast_lt.mpr hlt
    push_cast at hltR ⊢
    linarith
  have hcast : ((Nat.sqrt (3 * n + 1) - 8 : ℕ) : ℝ) = (Nat.sqrt (3 * n + 1) : ℝ) - 8 := by
    have h8 : (8 : ℕ) ≤ Nat.sqrt (3 * n + 1) := by omega
    rw [Nat.cast_sub h8]
    norm_num
  have hsq : (Real.sqrt ((3 * n + 1 : ℕ) : ℝ) - 9) ^ 2
      ≤ ((Nat.sqrt (3 * n + 1) - 8 : ℕ) : ℝ) ^ 2 := by
    rw [hcast]
    nlinarith [hsqrt9, hsqrtlt]
  have hfinal : ((3 * n + 1 : ℕ) : ℝ) < ((Nat.sqrt (3 * n + 1) - 8 : ℕ) : ℝ) ^ 2 +
      27 * (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ^ 2 := by
    linarith [hkey, hsq]
  exact_mod_cast hfinal

/-- `s₃(n) ≤ 40 n^{1/4}` for every `n ≥ 1`.

The two halves above give `s₃(n) ≤ 6⌊(3n+1)^{1/4}⌋ + 2` for `n ≥ 27`, and
`(3n+1)^{1/4} ≤ (4n)^{1/4} < 2 n^{1/4}`, so `s₃(n) ≤ 12 n^{1/4} + 2 ≤ 14 n^{1/4}`. The constant
`40` absorbs that slack together with the finitely many `n < 27`, where the crude bound
`s₃(n) ≤ n/3 ≤ 8` suffices. -/
@[zf_tag "lem_s3_bound"]
theorem s3_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (s3 n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  refine ⟨40, by norm_num, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht4 : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (n : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hn0]
    norm_num
  have ht1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hn1 (by norm_num)
  by_cases h27 : 27 ≤ n
  · have hs : s3 n ≤ 6 * ⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ + 2 :=
      s3_le_of_lt_sq_add h27 (lt_sq_add_floor_fourth_root h27)
    have hNR0 : (0 : ℝ) ≤ ((3 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hu0 : (0 : ℝ) ≤ ((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hNR0 _
    have hu4 : (((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = ((3 * n + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hNR0]
      norm_num
    have hT0 : (0 : ℝ) ≤ (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) := Nat.cast_nonneg _
    have hTle : (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ)
        ≤ ((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := Nat.floor_le hu0
    have hTpow : (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ^ 4 ≤ ((3 * n + 1 : ℕ) : ℝ) := by
      have h := pow_le_pow_left₀ hT0 hTle 4
      rw [hu4] at h
      exact h
    have hNle : ((3 * n + 1 : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by push_cast; linarith
    have hbig : (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 16 * (n : ℝ) := by
      rw [show (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 16 * ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 by ring,
        ht4]
    have hpow4 : (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ^ 4
        ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 := by
      rw [hbig]; linarith
    have hTb : (⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
      le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow4
    set T : ℕ := ⌊((3 * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌋₊ with hTdef
    have hsR : (s3 n : ℝ) ≤ 6 * (T : ℝ) + 2 := by exact_mod_cast hs
    linarith [hsR, hTb, ht1]
  · have hcrude : s3 n ≤ 8 := by have := s3_le n; omega
    have h8 : (s3 n : ℝ) ≤ 8 := by exact_mod_cast hcrude
    linarith [ht1, h8]

end ZeroFree
