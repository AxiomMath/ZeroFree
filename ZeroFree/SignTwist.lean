/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Abacus.Transpose
public import ZeroFree.Character
public import ZeroFree.Meta.Attr

/-!
# The sign twist

Transposing a bead set multiplies its Murnaghan--Nakayama value by the sign of the class:
`χ^{S†N}(w) = (-1)^{n-k} χ^S(w)`.

The proof is an induction on the list of part sizes. Each step reindexes the rim hooks of `S` onto
those of the transpose along the reflection `x ↦ N - 1 - (x - t)`, which is its own inverse there;
a rim hook of height `h` becomes one of height `t - 1 - h`, so every summand acquires the same
constant sign `(-1)^(t-1)` and it leaves the sum.

## Main results

* `card_transpose`: the transpose inside width `N` carries `N - S.card` beads.
* `beadSize_transpose_eq_zero_iff`: the transpose has size zero exactly when `S` does.
* `chi_transpose`: the sign twist.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- Reflection is injective on a bead set that fits the width, so the transpose carries the
complementary number of beads.

The injectivity is only *on* `S`: `(N - 1 - ·)` is not injective on all of `ℕ`, since truncated
subtraction collapses everything past `N - 1` to `0`, which is why `hS` is required. -/
theorem card_transpose {N : ℕ} {S : BeadSet} (hS : S ⊆ range N) :
    (transpose N S).card = N - S.card := by
  classical
  have himg : (S.image (fun s => N - 1 - s)) ⊆ range N := by
    intro y hy
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hy
    exact mem_range.mpr (by have := mem_range.mp (hS hsS); omega)
  have hcard : (S.image (fun s => N - 1 - s)).card = S.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have haN : a < N := mem_range.mp (hS (Finset.mem_coe.mp ha))
    have hbN : b < N := mem_range.mp (hS (Finset.mem_coe.mp hb))
    replace hab : N - 1 - a = N - 1 - b := hab
    omega
  simp only [transpose]
  rw [Finset.card_sdiff_of_subset himg, Finset.card_range, hcard]

/-- The transpose preserves having size zero, because reflecting an initial segment gives an
initial segment. -/
theorem beadSize_transpose_eq_zero_iff {N : ℕ} {S : BeadSet} (hS : S ⊆ range N) :
    beadSize (transpose N S) = 0 ↔ beadSize S = 0 := by
  classical
  have hle : S.card ≤ N := by
    simpa [Finset.card_range] using Finset.card_le_card hS
  have hk : (transpose N S).card = N - S.card := card_transpose hS
  rw [beadSize_eq_zero_iff, beadSize_eq_zero_iff]
  constructor
  · intro h
    have hback := transpose_transpose hS
    rw [h, transpose_range (by omega : (transpose N S).card ≤ N)] at hback
    have : N - (transpose N S).card = S.card := by omega
    rw [this] at hback
    exact hback.symm
  · intro h
    have hT : transpose N S = range (N - S.card) := by
      conv_lhs => rw [h]
      exact transpose_range hle
    rw [hT, Finset.card_range]

/-- Transposing multiplies the Murnaghan--Nakayama value by the sign of the class.

The exponent is `w.sum + w.length` rather than `n - k`: the two agree over `ℤ`, since they differ
by `(-1)^(2k) = 1`, and the additive form keeps truncated subtraction out of every rewrite. -/
@[zf_tag "lem_sign_twist"]
theorem chi_transpose {N : ℕ} :
    ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t) → ∀ S : BeadSet, S ⊆ range N →
      chi (transpose N S) w = (-1) ^ (w.sum + w.length) * chi S w := by
  intro w
  induction w with
  | nil =>
    intro _ S hS
    simp only [List.sum_nil, List.length_nil, Nat.add_zero, pow_zero, one_mul]
    rw [chi_nil, chi_nil]
    by_cases h : beadSize S = 0
    · rw [if_pos ((beadSize_transpose_eq_zero_iff hS).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((beadSize_transpose_eq_zero_iff hS).mp hc)), if_neg h]
  | cons t u ih =>
    intro hw S hS
    classical
    have ht : 1 ≤ t := hw t (List.mem_cons_self ..)
    have hu : ∀ s ∈ u, 1 ≤ s := fun s hs => hw s (List.mem_cons_of_mem _ hs)
    rw [chi_cons, chi_cons, Finset.mul_sum]
    refine (Finset.sum_nbij' (i := fun x => N - 1 - (x - t))
      (j := fun x => N - 1 - (x - t)) ?_ ?_ ?_ ?_ ?_).symm
    · intro x hx
      exact mem_chi_filter.mpr (isRimHook_transpose hS ht (mem_chi_filter.mp hx))
    · intro x' hx'
      have h2 := isRimHook_transpose (transpose_subset N S) ht (mem_chi_filter.mp hx')
      rw [transpose_transpose hS] at h2
      exact mem_chi_filter.mpr h2
    · intro x hx
      obtain ⟨hxS, htx, -⟩ := mem_chi_filter.mp hx
      have := mem_range.mp (hS hxS)
      omega
    · intro x' hx'
      obtain ⟨hxT, htx, -⟩ := mem_chi_filter.mp hx'
      have := mem_range.mp (transpose_subset N S hxT)
      omega
    · intro x hx
      obtain hr := mem_chi_filter.mp hx
      have hht := rimHookHeight_transpose_add hS ht hr
      have hrem := rimHookRemoval_transpose hS ht hr
      have hsub : rimHookRemoval t S x ⊆ range N := by
        obtain ⟨hxS, htx, -⟩ := hr
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact mem_range.mpr (by have := mem_range.mp (hS hxS); omega)
        · exact hS (Finset.mem_of_mem_erase hy')
      rw [hrem, ih hu _ hsub]
      have hsq : ((-1 : ℤ)) ^ rimHookHeight t S x * (-1) ^ rimHookHeight t S x = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨_, rfl⟩
      have hpow : ((-1 : ℤ)) ^ rimHookHeight t (transpose N S) (N - 1 - (x - t))
          = (-1) ^ (t - 1) * (-1) ^ rimHookHeight t S x := by
        have hsplit : ((-1 : ℤ)) ^ (t - 1)
            = (-1) ^ rimHookHeight t (transpose N S) (N - 1 - (x - t))
              * (-1) ^ rimHookHeight t S x := by
          rw [← pow_add, hht]
        rw [hsplit, mul_assoc, hsq, mul_one]
      rw [hpow]
      have hexp : (t :: u).sum + (t :: u).length
          = ((t - 1) + (u.sum + u.length)) + 2 := by
        have h1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
        simp only [List.sum_cons, List.length_cons]
        omega
      rw [hexp, pow_add, pow_add]
      norm_num
      ring

end ZeroFree
