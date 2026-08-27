/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Sieve.SetA
public import ZeroFree.Arithmetic.CoreDistance

/-!
# The tail estimate for the 3-core distance

For `1 < γ < 3/2`, the number of `n ≤ X` with `s₃(n) > S` is
`O(S + X (log X) ^ (5/6 (γ-1)) S ^ (1-γ))`. The proof is a counting argument over the gaps of
`SetB r`, fed by `setB_gaps`, and it is where the sieve side (`ZeroFree.Sieve.SetA`) and the
`3`-core distance side (`ZeroFree.Arithmetic.CoreDistance`) meet.

## Main results

* `setB_avoids_interval`: if `s₃(n) > S` and `N = 3n + 1 ≡ r mod 9`, then `SetB r` misses
  `[N - 9S, N]`.
* `self_le_rpow_mul_rpow`: `g ≤ a ^ (1 - γ) * g ^ γ` for `0 < a ≤ g` and `γ > 1`.
* `three_mul_add_one_bounds`: `3X + 1 ≤ 4X` and `log (3X + 1) ≤ 3 log X`, for `X ≥ 3`.
* `card_residue_class_Ioo`: the integers in `Ioo a b` lying in a fixed class mod `9` number at most
  `(b - a) / 9 + 1`.
* `exists_nth_bracket`: an integer with an element of an infinite set below it lies in
  `Ioc (nth p i) (nth p (i + 1))` for some `i`.
* `tail_bound`: the tail estimate.
-/

@[expose] public section

namespace ZeroFree

/-- **The interval `[N - 9S, N]` misses `SetB r` when `s₃(n) > S`**, where `N = 3n + 1`.

This is the geometric heart of the tail estimate, and the one step that uses anything about `s₃`.

If `s₃(n) > S` then no `s ≤ S` is an admissible `3`-shift, and it is always the Loeschian condition
in `shifts3` that fails, never the size condition: `3s ≤ 3S < 3 s₃(n) ≤ n` by `s3_mem`. So
`3(n - 3s) + 1 ∉ Lo` for every `s ≤ S`.

Any `m ∈ SetB r` in `[N - 9S, N]` contradicts that: `mem_setB_mod_nine` gives `m ≡ r ≡ N mod 9`, so
`m = N - 9s` with `s ≤ S`, and `mem_setB_loeschian` gives `m ∈ Lo`. -/
theorem setB_avoids_interval (L : LiteratureInputs) {r : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) {n S : ℕ}
    (hres : (3 * n + 1) ≡ r [MOD 9]) (hgt : S < s3 n) :
    ∀ m ∈ SetB r, ¬ (3 * n + 1 - 9 * S ≤ m ∧ m ≤ 3 * n + 1) := by
  intro m hmB hmem
  obtain ⟨hlo, hhi⟩ := hmem
  -- `m ≡ N mod 9` with `N - 9S ≤ m ≤ N`, so `m = N - 9s` for some `s ≤ S`.
  have hmr : m ≡ r [MOD 9] := mem_setB_mod_nine hmB
  have hmN : m ≡ 3 * n + 1 [MOD 9] := hmr.trans hres.symm
  obtain ⟨s, hsS, hms⟩ : ∃ s : ℕ, s ≤ S ∧ m = 3 * n + 1 - 9 * s := by
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hhi).mp hmN
    exact ⟨k, by omega, by omega⟩
  -- The size condition holds at `s`; hence it is the Loeschian one that fails.
  have hsize : 3 * s ≤ n := by have h1 : 3 * s3 n ≤ n := (s3_mem n).1; omega
  have hnotLo : ¬ Loeschian (3 * (n - 3 * s) + 1) := by
    intro hLo
    have : s3 n ≤ s := Nat.sInf_le (⟨hsize, hLo⟩ : s ∈ shifts3 n)
    omega
  have hmeq : m = 3 * (n - 3 * s) + 1 := by omega
  exact hnotLo (hmeq ▸ mem_setB_loeschian L hr hmB)


/-- **The exponent-splitting step.** For `0 < a ≤ g` and `γ > 1`,

`g ≤ a ^ (1 - γ) * g ^ γ`.

This converts a bound on the `γ`-th moment of the gaps into a bound on their plain sum, restricted
to gaps exceeding a threshold. Written `g = g ^ (1-γ) * g ^ γ` and then, since `1 - γ < 0` makes
`u ↦ u ^ (1-γ)` antitone, `g ^ (1-γ) ≤ a ^ (1-γ)`.

It is applied with `a = 9S` at gaps `g > 9S`, which is where the threshold hypothesis is spent:
without `a ≤ g` the inequality is false, and `setB_avoids_interval` is what supplies it. -/
theorem self_le_rpow_mul_rpow {a g γ : ℝ} (ha : 0 < a) (hag : a ≤ g) (hγ : 1 < γ) :
    g ≤ a ^ (1 - γ) * g ^ γ := by
  have hg : 0 < g := lt_of_lt_of_le ha hag
  have hexp : 1 - γ ≤ 0 := by linarith
  have hanti : g ^ (1 - γ) ≤ a ^ (1 - γ) := Real.rpow_le_rpow_of_nonpos ha hag hexp
  have hsplit : g ^ (1 - γ) * g ^ γ = g := by
    rw [← Real.rpow_add hg]
    norm_num
  calc g = g ^ (1 - γ) * g ^ γ := hsplit.symm
    _ ≤ a ^ (1 - γ) * g ^ γ :=
        mul_le_mul_of_nonneg_right hanti (Real.rpow_pos_of_pos hg γ).le

/-- **The `log` and linear relaxations needed at `3X + 1`.**

`setB_gaps` is applied at `3X + 1` rather than `X`, since the relevant elements of `SetB r` run up
to `N = 3n + 1 ≤ 3X + 1`. Pulling the bound back to `X` needs `3X + 1 ≤ 4X` and a
`log (3X + 1) ≤ c · log X`, both for `X ≥ 3`; the exponent `5/6 (γ - 1)` being nonnegative for
`γ ≥ 1` is what lets the second be used monotonically.

The constant `c = 3` cannot be lowered to `2` on this range: `log (3X + 1) ≤ 2 log X` is
`3X + 1 ≤ X ^ 2`, which at `X = 3` reads `10 ≤ 9` (numerically `log 10 ≈ 2.303` against
`2 log 3 ≈ 2.197`), and it first holds at `X = (3 + √13)/2 ≈ 3.30`. At `c = 3` the inequality is
`3X + 1 ≤ X ^ 3`, which at `X = 3` reads `10 ≤ 27`; either constant is absorbed downstream. -/
theorem three_mul_add_one_bounds {X : ℝ} (hX : 3 ≤ X) :
    3 * X + 1 ≤ 4 * X ∧ Real.log (3 * X + 1) ≤ 3 * Real.log X := by
  refine ⟨by linarith, ?_⟩
  have hX0 : (0 : ℝ) < X := by linarith
  -- `X ^ 3 - 3X - 1 ≥ 0` for `X ≥ 3`.
  have hcube : 3 * X + 1 ≤ X ^ 3 := by
    nlinarith [sq_nonneg X, sq_nonneg (X - 3), mul_nonneg (sub_nonneg.mpr hX) (sq_nonneg X)]
  have hpos : (0 : ℝ) < 3 * X + 1 := by linarith
  have h1 : Real.log (3 * X + 1) ≤ Real.log (X ^ 3) := by gcongr
  rwa [Real.log_pow, Nat.cast_ofNat] at h1


/-- **Counting a residue class in an interval.** The integers in `Ioo a b` that
are `≡ r mod 9` number at most `(b - a) / 9 + 1`.

This is the fibre bound for the tail estimate's injection: each qualifying `n` sends `N = 3n + 1`
strictly between two consecutive elements of `SetB r`, distinct `n` give distinct `N`, so the
number of `n` landing in one gap is at most the number of `N ≡ r mod 9` inside it.

Proved by injecting the class into `Finset.range ((b - a) / 9 + 1)` via `m ↦ (m - a - 1) / 9`.
Injectivity is the residue condition doing its work: two members of one class differ by a multiple
of `9`, and landing in the same block of nine forces that multiple to be `0`. -/
theorem card_residue_class_Ioo (a b r : ℕ) :
    ((Finset.Ioo a b).filter (fun m => m % 9 = r % 9)).card ≤ (b - a) / 9 + 1 := by
  classical
  rw [← Finset.card_range ((b - a) / 9 + 1)]
  apply Finset.card_le_card_of_injOn (fun m => (m - a - 1) / 9)
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo] at hm
    obtain ⟨⟨hma, hmb⟩, -⟩ := hm
    simp only [Finset.coe_range, Set.mem_Iio]
    -- `m - a - 1 ≤ b - a`, so the index is at most `(b - a) / 9`.
    have hle : m - a - 1 ≤ b - a := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioo] at hx hy
    obtain ⟨⟨hxa, hxb⟩, hxr⟩ := hx
    obtain ⟨⟨hya, hyb⟩, hyr⟩ := hy
    have hidx : (x - a - 1) / 9 = (y - a - 1) / 9 := hxy
    -- Same block of nine: the two indices agree, so the values differ by < 9.
    have hbx := Nat.div_add_mod (x - a - 1) 9
    have hby := Nat.div_add_mod (y - a - 1) 9
    omega


/-- **Bracketing an integer between consecutive elements.** For an infinite `p`
and any `N` with at least one element of `p` strictly below it, there is an index
`i` with `nth p i < N ≤ nth p (i + 1)`.

This turns each qualifying `n` into a *gap index*: the gap `nth p (i+1) - nth p i` containing
`N = 3n + 1` is the one whose length `setB_avoids_interval` forces to exceed `9S`.

The witness is `count p N - 1`, and the two halves come from opposite directions:
`Nat.nth_lt_of_lt_count` for the left, `Nat.le_nth_count` for the right. The hypothesis
`0 < count p N` is what makes `count p N - 1` meaningful in `ℕ`, and it holds here because
`r ∈ SetB r` with `r < N - 9S`. -/
theorem exists_nth_bracket {p : ℕ → Prop} [DecidablePred p]
    (hp : (Set.ofPred p).Infinite) {N : ℕ} (hN : 0 < Nat.count p N) :
    ∃ i, Nat.nth p i < N ∧ N ≤ Nat.nth p (i + 1) := by
  refine ⟨Nat.count p N - 1, Nat.nth_lt_of_lt_count (by omega), ?_⟩
  have hcnt := Nat.le_nth_count hp N
  have hi : Nat.count p N - 1 + 1 = Nat.count p N := by omega
  rw [hi]
  exact hcnt


/-! ### The counting half of the tail estimate

The remaining work is bookkeeping: split the count by the residue `r` of `N = 3n + 1` mod `9`,
discard the finitely many small `N` into the `O(S)` term, send each surviving `n` to the index of
the gap of `SetB r` that contains `N`, bound each fibre by the gap length, and feed the resulting
sum of gaps to `setB_gaps` through the exponent split. -/

/-- `1 ∈ SetA`, which is what makes `r ∈ SetB r`, so that every `N` past the small range has an
element of `SetB r` below `N - 9S` and hence a well-defined bracketing index. -/
private theorem one_mem_setA : (1 : ℕ) ∈ SetA := by
  refine ⟨le_refl 1, by norm_num, fun p _ _ => ?_⟩
  simp

/-- **The bracketing step, at one qualifying `n`.** For `r ∈ {1,4,7}`, an `n` with `s₃(n) > S`
whose `N = 3n + 1` is `≡ r mod 9` and exceeds `9S + 10` determines an index `i` with

`nth (SetB r) i + 9S < N < nth (SetB r) (i + 1)`.

Both endpoints are strict, and both strictnesses come from `setB_avoids_interval`: the left because
`nth _ i ≤ N` forces `¬ (N - 9S ≤ nth _ i)`, the right because `N ∉ SetB r` rules out equality with
`nth _ (i + 1)`. In particular the gap at `i` exceeds `9S`. -/
private theorem exists_gap_index (L : LiteratureInputs) {r : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) {n S : ℕ} (hres : (3 * n + 1) % 9 = r)
    (hgt : S < s3 n) (hbig : 9 * S + 10 < 3 * n + 1) :
    ∃ i, Nat.nth (fun x => x ∈ SetB r) i + 9 * S < 3 * n + 1 ∧
      3 * n + 1 < Nat.nth (fun x => x ∈ SetB r) (i + 1) := by
  have hr1 : 1 ≤ r := by rcases hr with rfl | rfl | rfl <;> omega
  have hr9 : r < 9 := by rcases hr with rfl | rfl | rfl <;> omega
  have hinf : (Set.ofPred (fun x => x ∈ SetB r)).Infinite := setB_infinite hr1
  have hmemr : r ∈ SetB r := ⟨1, one_mem_setA, (mul_one r).symm⟩
  -- `r < N`, so at least one element of `SetB r` sits below `N`.
  have hrN : r < 3 * n + 1 := by omega
  haveI : DecidablePred (fun x => x ∈ SetB r) := Classical.decPred _
  have hcnt : 0 < Nat.count (fun x => x ∈ SetB r) (3 * n + 1) :=
    Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr ⟨r, hrN, hmemr⟩)
  obtain ⟨i, hlt, hle⟩ := exists_nth_bracket (p := fun x => x ∈ SetB r) hinf hcnt
  have hresMod : (3 * n + 1) ≡ r [MOD 9] := by
    unfold Nat.ModEq
    rw [hres, Nat.mod_eq_of_lt hr9]
  have havoid := setB_avoids_interval L hr hresMod hgt
  refine ⟨i, ?_, ?_⟩
  · -- Left endpoint: `nth _ i ≤ N`, so the avoidance forces it below `N - 9S`.
    have hmem : Nat.nth (fun x => x ∈ SetB r) i ∈ SetB r :=
      Nat.nth_mem_of_infinite (p := fun x => x ∈ SetB r) hinf i
    have := havoid _ hmem
    omega
  · -- Right endpoint: `N ∉ SetB r`, so `N ≠ nth _ (i + 1)`.
    have hmem : Nat.nth (fun x => x ∈ SetB r) (i + 1) ∈ SetB r :=
      Nat.nth_mem_of_infinite (p := fun x => x ∈ SetB r) hinf (i + 1)
    rcases Nat.lt_or_ge (3 * n + 1) (Nat.nth (fun x => x ∈ SetB r) (i + 1)) with h | h
    · exact h
    · have heq : Nat.nth (fun x => x ∈ SetB r) (i + 1) = 3 * n + 1 := by omega
      exact absurd (havoid _ hmem) (by simp [heq])

/-- **The fibre bound, in the shape the summation wants.** A gap longer than `9S ≥ 9` contains at
most `g` integers of a fixed class mod `9`, where `g` is its length — the crude relaxation of
`card_residue_class_Ioo`'s `g / 9 + 1` that keeps the summand equal to the gap itself. -/
private theorem fibre_card_le_gap (r a b S : ℕ) (hS : 1 ≤ S) (hgap : 9 * S < b - a) :
    ((Finset.Ioo a b).filter (fun m => m % 9 = r % 9)).card ≤ b - a := by
  have h := card_residue_class_Ioo a b r
  have hd := Nat.div_add_mod (b - a) 9
  have hm : (b - a) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  omega

/-- **The counting step, for one residue `r`.** Any finite set `s` of integers `n` with
`s₃(n) > S`, `3n + 1 ≡ r mod 9`, `3n + 1 > 9S + 10` and `3n + 1 ≤ Y` has at most `∑ g_i` elements,
the sum running over the indices `i` that `setB_gaps` sums over at `Y` and whose gap exceeds `9S`.

The map is `n ↦ 3n + 1`, injective, landing in the union over those `i` of the class `≡ r mod 9`
inside the open gap `(b_i, b_{i+1})`; `exists_gap_index` produces the index and the two strict
inequalities, `Finset.card_biUnion_le` splits the union, and `fibre_card_le_gap` bounds each piece
by its gap. The index really is in range: `i ≤ b_i` because `Nat.nth` is strictly monotone, and
`b_i < 3n + 1 ≤ Y`. -/
private theorem card_le_gap_sum (L : LiteratureInputs) {r : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) {S : ℕ} (hS : 1 ≤ S) {Y : ℝ} (s : Finset ℕ)
    (hs3 : ∀ n ∈ s, S < s3 n) (hres : ∀ n ∈ s, (3 * n + 1) % 9 = r)
    (hbig : ∀ n ∈ s, 9 * S + 10 < 3 * n + 1)
    (hle : ∀ n ∈ s, ((3 * n + 1 : ℕ) : ℝ) ≤ Y) :
    s.card ≤ ∑ i ∈ ((Finset.range (⌊Y⌋₊ + 1)).filter
        (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ Y)).filter
        (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
          - Nat.nth (fun x => x ∈ SetB r) i),
      (Nat.nth (fun x => x ∈ SetB r) (i + 1) - Nat.nth (fun x => x ∈ SetB r) i) := by
  have hr1 : 1 ≤ r := by rcases hr with rfl | rfl | rfl <;> omega
  have hr9 : r < 9 := by rcases hr with rfl | rfl | rfl <;> omega
  have hinf : (Set.ofPred (fun x => x ∈ SetB r)).Infinite := setB_infinite hr1
  set G := ((Finset.range (⌊Y⌋₊ + 1)).filter
      (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ Y)).filter
      (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
        - Nat.nth (fun x => x ∈ SetB r) i) with hG
  have step1 : s.card ≤ (G.biUnion (fun i =>
      (Finset.Ioo (Nat.nth (fun x => x ∈ SetB r) i)
        (Nat.nth (fun x => x ∈ SetB r) (i + 1))).filter
        (fun m => m % 9 = r % 9))).card := by
    refine Finset.card_le_card_of_injOn (fun n => 3 * n + 1) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe] at hn ⊢
      obtain ⟨i, hleft, hright⟩ := exists_gap_index L hr (hres n hn) (hs3 n hn) (hbig n hn)
      have hltN : Nat.nth (fun x => x ∈ SetB r) i < 3 * n + 1 := by omega
      have hcast : (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ Y :=
        (Nat.cast_le.mpr hltN.le).trans (hle n hn)
      have hiG : i ∈ G := by
        have hfloor : Nat.nth (fun x => x ∈ SetB r) i ≤ ⌊Y⌋₊ := Nat.le_floor hcast
        have hidx : i ≤ Nat.nth (fun x => x ∈ SetB r) i :=
          (Nat.nth_strictMono hinf).le_apply
        rw [hG]
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, hcast⟩, by omega⟩
      refine Finset.mem_biUnion.mpr ⟨i, hiG, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_Ioo]
      refine ⟨⟨hltN, hright⟩, ?_⟩
      rw [Nat.mod_eq_of_lt hr9]
      exact hres n hn
    · intro x _ y _ hxy
      have h : 3 * x + 1 = 3 * y + 1 := hxy
      omega
  refine step1.trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_))
  intro i hi
  rw [hG] at hi
  exact fibre_card_le_gap r _ _ S hS (Finset.mem_filter.mp hi).2

/-- **The summation step, for one residue `r`.** The sum of the gaps of `SetB r` below `3X + 1`
that exceed `9S` is `O(X (log X) ^ (5/6 (γ-1)) S ^ (1-γ))`.

Three moves, in order: `self_le_rpow_mul_rpow` at `a = 9S` trades each gap `g` for
`(9S) ^ (1-γ) g ^ γ` — legitimate exactly because the sum is restricted to `g > 9S`; dropping the
restriction (the terms being nonnegative) exposes `setB_gaps`, applied at `3X + 1`; and
`three_mul_add_one_bounds` pulls `3X + 1` and `log (3X + 1)` back to `X` and `log X`, the `log`
step needing the exponent `5/6 (γ - 1) ≥ 0`. -/
private theorem gap_sum_bound (L : LiteratureInputs) {r : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 3 ≤ X → ∀ S : ℕ, 1 ≤ S →
      ∑ i ∈ ((Finset.range (⌊(3 * X + 1 : ℝ)⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ 3 * X + 1)).filter
          (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
          - Nat.nth (fun x => x ∈ SetB r) i : ℕ) : ℝ)
        ≤ D * (X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ)) := by
  have hr1 : 1 ≤ r := by rcases hr with rfl | rfl | rfl <;> omega
  have hinf : (Set.ofPred (fun x => x ∈ SetB r)).Infinite := setB_infinite hr1
  obtain ⟨C₁, hC₁, hB⟩ := setB_gaps L hr hγ1.le hγ2
  have he : (0 : ℝ) ≤ (5 : ℝ) / 6 * (γ - 1) := by nlinarith
  refine ⟨(9 : ℝ) ^ (1 - γ) * C₁ * 4 * 3 ^ ((5 : ℝ) / 6 * (γ - 1)), by positivity, ?_⟩
  intro X hX S hS
  obtain ⟨hlin, hlog⟩ := three_mul_add_one_bounds hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hY3 : (3 : ℝ) ≤ 3 * X + 1 := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : (0 : ℝ) ≤ Real.log (3 * X + 1) := Real.log_nonneg (by linarith)
  have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  -- The gap, as a natural number cast, is the real difference.
  have hmono : ∀ i : ℕ, Nat.nth (fun x => x ∈ SetB r) i
      ≤ Nat.nth (fun x => x ∈ SetB r) (i + 1) := fun i => Nat.nth_monotone hinf (by omega)
  have hcastgap : ∀ i : ℕ, ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
      - Nat.nth (fun x => x ∈ SetB r) i : ℕ) : ℝ)
        = (Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
          - (Nat.nth (fun x => x ∈ SetB r) i : ℝ) := fun i => Nat.cast_sub (hmono i)
  have hgapnn : ∀ i : ℕ, (0 : ℝ) ≤ (Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
      - (Nat.nth (fun x => x ∈ SetB r) i : ℝ) := by
    intro i
    have := Nat.cast_le (α := ℝ) |>.mpr (hmono i)
    linarith
  -- The `log` relaxation, at the nonnegative exponent.
  have hlogpow : Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))
      ≤ 3 ^ ((5 : ℝ) / 6 * (γ - 1)) * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) := by
    calc Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))
        ≤ (3 * Real.log X) ^ ((5 : ℝ) / 6 * (γ - 1)) := Real.rpow_le_rpow hlogY hlog he
      _ = 3 ^ ((5 : ℝ) / 6 * (γ - 1)) * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) :=
          Real.mul_rpow (by norm_num) hlogX.le
  calc ∑ i ∈ ((Finset.range (⌊(3 * X + 1 : ℝ)⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ 3 * X + 1)).filter
          (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
          - Nat.nth (fun x => x ∈ SetB r) i : ℕ) : ℝ)
      ≤ ∑ i ∈ ((Finset.range (⌊(3 * X + 1 : ℝ)⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ 3 * X + 1)).filter
          (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i),
        (9 * (S : ℝ)) ^ (1 - γ) * ((Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
          - (Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hgapN : 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i := (Finset.mem_filter.mp hi).2
        have ha : (0 : ℝ) < 9 * (S : ℝ) := by linarith
        have hag : 9 * (S : ℝ) ≤ (Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
            - (Nat.nth (fun x => x ∈ SetB r) i : ℝ) := by
          rw [← hcastgap i]
          have : ((9 * S : ℕ) : ℝ) ≤ ((Nat.nth (fun x => x ∈ SetB r) (i + 1)
              - Nat.nth (fun x => x ∈ SetB r) i : ℕ) : ℝ) := Nat.cast_le.mpr hgapN.le
          push_cast at this
          linarith
        rw [hcastgap i]
        exact self_le_rpow_mul_rpow ha hag hγ1
    _ = (9 * (S : ℝ)) ^ (1 - γ) * ∑ i ∈ ((Finset.range (⌊(3 * X + 1 : ℝ)⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ 3 * X + 1)).filter
          (fun i => 9 * S < Nat.nth (fun x => x ∈ SetB r) (i + 1)
            - Nat.nth (fun x => x ∈ SetB r) i),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
          - (Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ := by
        rw [Finset.mul_sum]
    _ ≤ (9 * (S : ℝ)) ^ (1 - γ) * ∑ i ∈ (Finset.range (⌊(3 * X + 1 : ℝ)⌋₊ + 1)).filter
          (fun i => (Nat.nth (fun x => x ∈ SetB r) i : ℝ) ≤ 3 * X + 1),
        ((Nat.nth (fun x => x ∈ SetB r) (i + 1) : ℝ)
          - (Nat.nth (fun x => x ∈ SetB r) i : ℝ)) ^ γ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Real.rpow_nonneg (hgapnn i) _)
    _ ≤ (9 * (S : ℝ)) ^ (1 - γ)
          * (C₁ * (3 * X + 1) * Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))) :=
        mul_le_mul_of_nonneg_left (hB (3 * X + 1) hY3) (Real.rpow_nonneg (by positivity) _)
    _ ≤ (9 : ℝ) ^ (1 - γ) * C₁ * 4 * 3 ^ ((5 : ℝ) / 6 * (γ - 1))
          * (X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ)) := by
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg S)]
        have hK : (0 : ℝ) ≤ (9 : ℝ) ^ (1 - γ) * (S : ℝ) ^ (1 - γ) := by positivity
        have hstep : C₁ * (3 * X + 1) * Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))
            ≤ C₁ * (4 * X) * (3 ^ ((5 : ℝ) / 6 * (γ - 1))
              * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1))) := by
          have hLnn : (0 : ℝ) ≤ Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1)) :=
            Real.rpow_nonneg hlogY _
          have h1 : C₁ * (3 * X + 1) * Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))
              ≤ C₁ * (4 * X) * Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hC₁.le) hLnn
          have h2 : C₁ * (4 * X) * Real.log (3 * X + 1) ^ ((5 : ℝ) / 6 * (γ - 1))
              ≤ C₁ * (4 * X) * (3 ^ ((5 : ℝ) / 6 * (γ - 1))
                * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1))) :=
            mul_le_mul_of_nonneg_left hlogpow (by positivity)
          linarith
        refine le_trans (mul_le_mul_of_nonneg_left hstep hK) ?_
        have hring : (9 : ℝ) ^ (1 - γ) * (S : ℝ) ^ (1 - γ) * (C₁ * (4 * X)
              * (3 ^ ((5 : ℝ) / 6 * (γ - 1)) * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1))))
            = (9 : ℝ) ^ (1 - γ) * C₁ * 4 * 3 ^ ((5 : ℝ) / 6 * (γ - 1))
              * (X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ)) := by
          ring
        linarith [hring]

/-- **The residue split, plus the `O(S)` term.** For any predicate `P`, the count of `n ∈ [1, M]`
with `P n` is at most `3S + 3` plus the counts of those `n` that additionally satisfy
`3n + 1 > 9S + 10` and `3n + 1 ≡ r mod 9`, summed over `r ∈ {1,4,7}`.

Two facts are in play. `N = 3n + 1 ≡ 1 mod 3` forces `N mod 9 ∈ {1,4,7}`, so the three residues
exhaust the large `n`. And `3n + 1 ≤ 9S + 10` forces `n ≤ 3S + 3`, so the small `n` fit inside
`Icc 1 (3S + 3)`, a crude `O(S)` bound. -/
private theorem card_residue_split (M S : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.Icc 1 M).filter P).card
      ≤ 3 * S + 3 + ∑ r ∈ ({1, 4, 7} : Finset ℕ),
          ((Finset.Icc 1 M).filter
            (fun n => P n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)).card := by
  have hsub : (Finset.Icc 1 M).filter P ⊆
      Finset.Icc 1 (3 * S + 3) ∪ ({1, 4, 7} : Finset ℕ).biUnion (fun r =>
        (Finset.Icc 1 M).filter
          (fun n => P n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hP⟩ := hn
    by_cases hsm : 3 * n + 1 ≤ 9 * S + 10
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, by omega⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(3 * n + 1) % 9, ?_, ?_⟩)
      · -- `N ≡ 1 mod 3`, so `N mod 9 ∈ {1,4,7}`.
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hn1, hn2⟩, hP, rfl, by omega⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 : (Finset.Icc 1 (3 * S + 3)).card = 3 * S + 3 := by simp
  have h2 := Finset.card_biUnion_le (s := ({1, 4, 7} : Finset ℕ)) (t := fun r =>
      (Finset.Icc 1 M).filter
        (fun n => P n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1))
  omega

/-- **The bound for one residue class, large `N`.** Composes the counting step with the summation
step: `card_le_gap_sum` replaces the count by a sum of gaps of `SetB r` below `3X + 1`, and
`gap_sum_bound` evaluates that sum. The only glue is the cast of the `ℕ`-valued count and sum into
`ℝ`, and the observation that `n ≤ ⌊X⌋₊` gives `3n + 1 ≤ 3X + 1` as reals. -/
private theorem card_big_bound (L : LiteratureInputs) {r : ℕ}
    (hr : r = 1 ∨ r = 4 ∨ r = 7) {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 3 ≤ X → ∀ S : ℕ, 1 ≤ S →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n => S < s3 n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)).card : ℝ)
        ≤ D * (X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ)) := by
  obtain ⟨D, hD, hgs⟩ := gap_sum_bound L hr hγ1 hγ2
  refine ⟨D, hD, ?_⟩
  intro X hX S hS
  refine le_trans ?_ (hgs X hX S hS)
  rw [← Nat.cast_sum]
  refine Nat.cast_le.mpr (card_le_gap_sum L hr hS (Y := 3 * X + 1) _
    (fun n hn => (Finset.mem_filter.mp hn).2.1)
    (fun n hn => (Finset.mem_filter.mp hn).2.2.1)
    (fun n hn => (Finset.mem_filter.mp hn).2.2.2) (fun n hn => ?_))
  have hnM : n ≤ ⌊X⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have h1 : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := Nat.cast_le.mpr hnM
  have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  push_cast
  linarith

/-- **The tail estimate for the `3`-core distance.** For `1 < γ < 3/2` there is `C > 0` with

`#{1 ≤ n ≤ X : s₃(n) > S} ≤ C (S + X (log X) ^ (5/6 (γ-1)) S ^ (1-γ))`

for every real `X ≥ 3` and every integer `S ≥ 1`.

Writing `N = 3n + 1`, the count splits by `N mod 9 ∈ {1,4,7}` (`card_residue_split`, which also
peels off the `n` with `N ≤ 9S + 10` into the `O(S)` term). For each residue `r` and each surviving
`n`, `setB_avoids_interval` says `[N - 9S, N]` misses `SetB r`, so the bracketing index supplied by
`exists_nth_bracket` has a gap longer than `9S` (`exists_gap_index`); the fibre over a gap is a
residue class in an open interval, hence at most the gap length (`card_residue_class_Ioo`, relaxed
by `fibre_card_le_gap`); and `self_le_rpow_mul_rpow` at `a = 9S` turns the resulting sum of gaps
into the `γ`-th moment that `setB_gaps` bounds, with `three_mul_add_one_bounds` pulling `3X + 1`
back to `X`.

The constant is generous: `6 + 3(D₁ + D₄ + D₇)`, where the `6` absorbs `3S + 3 ≤ 6S` (valid since
`S ≥ 1`) and the three `D`'s are the per-residue constants. -/
@[zf_tag "prop_tail"]
theorem tail_bound (L : LiteratureInputs) {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X → ∀ S : ℕ, 1 ≤ S →
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun n => S < s3 n)).card : ℝ)
        ≤ C * ((S : ℝ) + X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ)) := by
  obtain ⟨D₁, hD₁, hb₁⟩ := card_big_bound L (r := 1) (Or.inl rfl) hγ1 hγ2
  obtain ⟨D₄, hD₄, hb₄⟩ := card_big_bound L (r := 4) (Or.inr (Or.inl rfl)) hγ1 hγ2
  obtain ⟨D₇, hD₇, hb₇⟩ := card_big_bound L (r := 7) (Or.inr (Or.inr rfl)) hγ1 hγ2
  refine ⟨6 + 3 * (D₁ + D₄ + D₇), by linarith, ?_⟩
  intro X hX S hS
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hSpos : (0 : ℝ) < (S : ℝ) := by linarith
  have k₁ := hb₁ X hX S hS
  have k₄ := hb₄ X hX S hS
  have k₇ := hb₇ X hX S hS
  set W := X * Real.log X ^ ((5 : ℝ) / 6 * (γ - 1)) * (S : ℝ) ^ (1 - γ) with hW
  have hWpos : (0 : ℝ) < W := by
    rw [hW]
    exact mul_pos (mul_pos hX0 (Real.rpow_pos_of_pos hlogX _))
      (Real.rpow_pos_of_pos hSpos _)
  set D := D₁ + D₄ + D₇ with hD
  have hDnn : (0 : ℝ) ≤ D := by rw [hD]; linarith
  have key : ∀ r ∈ ({1, 4, 7} : Finset ℕ),
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n => S < s3 n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)).card : ℝ)
        ≤ D * W := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact k₁.trans (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hWpos.le)
    · exact k₄.trans (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hWpos.le)
    · exact k₇.trans (mul_le_mul_of_nonneg_right (by rw [hD]; linarith) hWpos.le)
  have hsum : ∑ r ∈ ({1, 4, 7} : Finset ℕ),
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n => S < s3 n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)).card : ℝ)
        ≤ 3 * (D * W) := by
    refine (Finset.sum_le_sum key).trans ?_
    simp
  have hsplitR : (((Finset.Icc 1 ⌊X⌋₊).filter (fun n => S < s3 n)).card : ℝ)
      ≤ 3 * (S : ℝ) + 3 + ∑ r ∈ ({1, 4, 7} : Finset ℕ),
        (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n => S < s3 n ∧ (3 * n + 1) % 9 = r ∧ 9 * S + 10 < 3 * n + 1)).card : ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr (card_residue_split ⌊X⌋₊ S (fun n => S < s3 n))
    push_cast at h
    linarith
  have hexp : (6 + 3 * D) * ((S : ℝ) + W)
      = 6 * (S : ℝ) + 6 * W + 3 * D * (S : ℝ) + 3 * (D * W) := by ring
  linarith [mul_nonneg hDnn hSpos.le, hexp, hsplitR, hsum, hWpos]

end ZeroFree
