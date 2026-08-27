/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Abacus.Staircase
public import ZeroFree.Abacus.Weight
public import ZeroFree.Arithmetic.CoreDistance
public import ZeroFree.ChiPerm
public import ZeroFree.LiteratureInputs
public import ZeroFree.ThreeCore

/-!
# The core-removal cutoff

If `n - st` is the size of a `t`-core and `μ ⊢ n` has more than `s` parts equal to `t`, then some
`λ ⊢ n` has `χ^λ(μ) = 0`. At `s = 0` this says that a part of size at least four forces a zero,
and at `t = 2, 3` it bounds the number of parts equal to `2` and to `3` in a class with a
zero-free column.

## Main definitions

* `padBeads`: the reindexing `β_m(λ) ↦ β_{m+1}(λ)`, which adds a zero part to the partition.

## Main results

* `exists_chi_eq_zero_of_lt_count`: the core-removal cutoff.
* `exists_chi_eq_zero_of_four_le_part`: a part of size at least four forces a vanishing value.
* `count_three_le_s3`: a zero-free column has at most `s₃(n)` parts equal to `3`.
* `count_two_le_s2`: a zero-free column has at most `s₂(n)` parts equal to `2`.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- One rim-hook removal costs at least one unit of `t`-weight. -/
theorem wt_removal_succ_le {t : ℕ} (ht : 1 ≤ t) {S : BeadSet} {x : ℕ}
    (hx : IsRimHook t S x) :
    wt t (rimHookRemoval t S x) + 1 ≤ wt t S := by
  obtain ⟨T, hT⟩ := exists_rimHookChain_wt ht (rimHookRemoval t S x)
  exact no_long_chain ht (RimHookChain.step hx hT)

/-- More initial parts equal to `t` than the `t`-weight allows forces the character value to
vanish: the Murnaghan--Nakayama expansion along the initial `List.replicate r t` is indexed by
chains of `r` successive `t`-rim-hook removals, and by `no_long_chain` there are none. -/
theorem chi_replicate_eq_zero {t : ℕ} (ht : 1 ≤ t) {S : BeadSet} {r : ℕ} {v : List ℕ}
    (h : wt t S < r) : chi S (List.replicate r t ++ v) = 0 := by
  induction r generalizing S with
  | zero => omega
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append, chi_cons]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : IsRimHook t S x := mem_chi_filter.mp hx
    have := wt_removal_succ_le ht hx'
    rw [ih (by omega), mul_zero]

/-! ### Bringing the copies of `t` to the front -/

/-- The parts of a multiset, reordered with all copies of `t` first. -/
theorem toList_perm_replicate_append (m : Multiset ℕ) (t : ℕ) :
    m.toList.Perm (List.replicate (m.count t) t ++ (m.filter (· ≠ t)).toList) := by
  classical
  refine Multiset.coe_eq_coe.mp ?_
  rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_replicate,
    Multiset.coe_toList, ← Multiset.filter_eq' m t]
  exact (Multiset.filter_add_not (fun a => a = t) m).symm

/-! ### Padding a bead set with a zero part

Padding `S ↦ {0} ∪ (S + 1)` raises the bead count by one, leaves the size alone, and preserves
being a `t`-core. -/

/-- Padding a bead set with a zero part: every bead moves up one slot and a new bead occupies slot
`0`. This is the reindexing `β_m(λ) ↦ β_{m+1}(λ)`. -/
def padBeads (S : BeadSet) : BeadSet := insert 0 (S.image (· + 1))

variable {S : BeadSet}

theorem mem_padBeads {x : ℕ} : x ∈ padBeads S ↔ x = 0 ∨ ∃ y ∈ S, y + 1 = x := by
  simp [padBeads]

theorem zero_notMem_image_succ : 0 ∉ S.image (· + 1) := by
  simp

theorem card_padBeads (S : BeadSet) : (padBeads S).card = S.card + 1 := by
  rw [padBeads, Finset.card_insert_of_notMem zero_notMem_image_succ,
    Finset.card_image_of_injective _ (add_left_injective 1)]

theorem sum_padBeads (S : BeadSet) : ∑ x ∈ padBeads S, x = (∑ x ∈ S, x) + S.card := by
  rw [padBeads, Finset.sum_insert zero_notMem_image_succ,
    Finset.sum_image (fun a _ b _ h => by omega)]
  simp [Finset.sum_add_distrib]

theorem beadSize_padBeads (S : BeadSet) : beadSize (padBeads S) = beadSize S := by
  have h1 := size_beta S
  have h2 := size_beta (padBeads S)
  rw [card_padBeads, Finset.sum_range_succ, sum_padBeads] at h2
  omega

theorem isTCore_padBeads {t : ℕ} (ht : 1 ≤ t) (h : IsTCore t S) :
    IsTCore t (padBeads S) := by
  rintro x ⟨hx, htx, hsub⟩
  obtain rfl | ⟨y, hyS, rfl⟩ := mem_padBeads.mp hx
  · omega
  rcases Nat.lt_or_ge y t with hlt | hge
  · exact hsub (mem_padBeads.mpr (Or.inl (by omega)))
  refine h y ⟨hyS, hge, fun hmem => hsub (mem_padBeads.mpr (Or.inr ⟨y - t, hmem, by omega⟩))⟩

theorem card_padBeads_iterate (S : BeadSet) (k : ℕ) :
    (padBeads^[k] S).card = S.card + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', card_padBeads, ih]; omega

theorem beadSize_padBeads_iterate (S : BeadSet) (k : ℕ) :
    beadSize (padBeads^[k] S) = beadSize S := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', beadSize_padBeads, ih]

theorem isTCore_padBeads_iterate {t : ℕ} (ht : 1 ≤ t) (h : IsTCore t S) (k : ℕ) :
    IsTCore t (padBeads^[k] S) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Function.iterate_succ_apply']; exact isTCore_padBeads ht ih

/-! ### The first-row extension keeps the bead count and adds `st` to the size -/

variable {t s M : ℕ}

theorem card_extendTop (hM : M ∈ S) (hmax : ∀ y ∈ S, y ≤ M) :
    (extendTop t s M S).card = S.card := by
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨M, hM⟩
  rw [extendTop, Finset.card_insert_of_notMem (extend_notMem hmax),
    Finset.card_erase_of_mem hM]
  omega

theorem sum_extendTop (hM : M ∈ S) (hmax : ∀ y ∈ S, y ≤ M) :
    ∑ x ∈ extendTop t s M S, x = (∑ x ∈ S, x) + s * t := by
  have herase := Finset.add_sum_erase S (fun y => y) hM
  rw [extendTop, Finset.sum_insert (extend_notMem hmax)]
  omega

theorem beadSize_extendTop (hM : M ∈ S) (hmax : ∀ y ∈ S, y ≤ M) :
    beadSize (extendTop t s M S) = beadSize S + s * t := by
  have h1 := size_beta S
  have h2 := size_beta (extendTop t s M S)
  rw [card_extendTop hM hmax, sum_extendTop hM hmax] at h2
  omega

/-- *The core-removal cutoff.* If `n - st` is the size of a `t`-core and `μ ⊢ n` has more than `s`
parts equal to `t`, then some `λ ⊢ n` has `χ^λ(μ) = 0`.

`λ` is built from the `t`-core `γ` by adding `st` to its first part, which by `wt_extendTop` gives
`wt t λ = s`. Reordering `μ`'s parts to put its `r > s` copies of `t` first (`chi_perm`) exhibits
`χ^λ(μ)` as a sum indexed by chains of `r` successive `t`-rim-hook removals from `λ`, and by
`no_long_chain` there are none.

The hypothesis `γ.card ≤ n` is the encoding's shadow of "a partition of `m` has at most `m`
parts": a bead set carries its bead count as free data, so the bound has to be assumed rather
than derived. -/
@[zf_tag "lem_cutoff"]
theorem exists_chi_eq_zero_of_lt_count {t n s : ℕ} (ht : 2 ≤ t) (hn : 1 ≤ n)
    (hst : s * t ≤ n) {γ : BeadSet} (hγcard : γ.card ≤ n)
    (hγsize : beadSize γ = n - s * t) (hγcore : IsTCore t γ)
    (μ : Nat.Partition n) (hμ : s < μ.parts.count t) :
    ∃ S : BeadSet, S.card = n ∧ beadSize S = n ∧ chi S μ.parts.toList = 0 := by
  classical
  set P := padBeads^[n - γ.card] γ with hP
  have hPcard : P.card = n := by rw [hP, card_padBeads_iterate]; omega
  have hPsize : beadSize P = n - s * t := by rw [hP, beadSize_padBeads_iterate, hγsize]
  have hPcore : IsTCore t P := isTCore_padBeads_iterate (by omega) hγcore _
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hM : P.max' hPne ∈ P := P.max'_mem hPne
  have hmax : ∀ y ∈ P, y ≤ P.max' hPne := fun y hy => P.le_max' y hy
  refine ⟨extendTop t s (P.max' hPne) P, by rw [card_extendTop hM hmax, hPcard], ?_, ?_⟩
  · rw [beadSize_extendTop hM hmax, hPsize]; omega
  · have hwt : wt t (extendTop t s (P.max' hPne) P) = s :=
      wt_extendTop (by omega) hPcore hM hmax
    rw [chi_perm (toList_perm_replicate_append μ.parts t)]
    exact chi_replicate_eq_zero (by omega) (by rw [hwt]; exact hμ)

/-- *Parts of size at least four force a zero.* If `μ ⊢ n` has a part `t ≥ 4`, then some `λ ⊢ n`
has `χ^λ(μ) = 0`.

This is the cutoff at `s = 0`, where the `t`-core asked for has to have size `n`: once `t ≥ 4` a
`t`-core of *every* size exists. -/
@[zf_tag "lem_big_part"]
theorem exists_chi_eq_zero_of_four_le_part (L : LiteratureInputs) {t n : ℕ}
    (ht : 4 ≤ t) (hn : 1 ≤ n) (μ : Nat.Partition n) (hμ : t ∈ μ.parts) :
    ∃ S : BeadSet, S.card = n ∧ beadSize S = n ∧ chi S μ.parts.toList = 0 := by
  obtain ⟨γ, hcard, hsize, hcore⟩ := L.tcorePositivity ht n
  exact exists_chi_eq_zero_of_lt_count (s := 0) (by omega) hn (by omega) (by omega)
    (by omega) hcore μ (Multiset.count_pos.mpr hμ)

/-- *The bound on the number of `3`-cycles.* If `μ ⊢ n` has a zero-free column, then its number of
parts equal to `3` is at most `s₃(n)`.

The contrapositive of the cutoff at `t = 3`, `s = s₃(n)`, where `3 s₃(n) ≤ n` and
`3(n - 3 s₃(n)) + 1` is Loeschian, hence a `3`-core of size `n - 3 s₃(n)` exists. -/
@[zf_tag "lem_abound"]
theorem count_three_le_s3 (L : LiteratureInputs) {n : ℕ} (hn : 1 ≤ n)
    (μ : Nat.Partition n) (hμ : ZeroFreeColumn n μ) :
    μ.parts.count 3 ≤ s3 n := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨hle, hlo⟩ := s3_mem n
  obtain ⟨γ, hγcard, hγsize, hγcore⟩ :=
    (exists_isTCore_three_iff L (n - 3 * s3 n)).mpr hlo
  obtain ⟨S, hScard, hSsize, hSchi⟩ :=
    exists_chi_eq_zero_of_lt_count (t := 3) (s := s3 n) (by omega) hn (by omega)
      (by omega) (by omega) hγcore μ hlt
  exact hμ S hScard hSsize hSchi

/-- *The bound on the number of `2`-cycles.* If `μ ⊢ n` has a zero-free column, then its number of
parts equal to `2` is at most `s₂(n)`.

The cutoff at `t = 2`, `s = s₂(n)`, where `2 s₂(n) ≤ n` and `n - 2 s₂(n) = T_u` is triangular: the
staircase is a `2`-core of size `T_u` with `u` beads, and `u ≤ T_u`. -/
@[zf_tag "lem_bbound"]
theorem count_two_le_s2 {n : ℕ} (hn : 1 ≤ n) (μ : Nat.Partition n)
    (hμ : ZeroFreeColumn n μ) :
    μ.parts.count 2 ≤ s2 n := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨hle, u, hu⟩ := s2_mem n
  obtain ⟨γ, hγcard, hγsize, hγcore⟩ := exists_tcore_two_of_tri u
  have hut : u ≤ tri u := by
    have h2 := two_mul_tri u
    rcases Nat.eq_zero_or_pos u with rfl | hu1
    · simp [tri]
    · nlinarith
  obtain ⟨S, hScard, hSsize, hSchi⟩ :=
    exists_chi_eq_zero_of_lt_count (t := 2) (s := s2 n) (by omega) hn (by omega)
      (by omega) (by omega) hγcore μ hlt
  exact hμ S hScard hSsize hSchi

end ZeroFree
