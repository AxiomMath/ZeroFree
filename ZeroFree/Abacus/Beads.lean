/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import ZeroFree.Abacus.Descent
public import ZeroFree.Meta.Attr

/-!
# Bead sets, rim hooks, and removal

A partition with at most `m` parts and the set `{λ_i + m - i : 1 ≤ i ≤ m}` of `m` distinct
naturals are interchangeable data. Here the *bead set* is the primary object: `Finset ℕ` is the
carrier and `S.card` plays the role of `m`, and rim hooks, their heights and their removal are
all defined on the bead set.

A rim hook of length `t` is an admissible bead — one that can move `t` places left into an
unoccupied slot — and its removal is that move. At `t = 1` it is exactly a descent in the sense
of `ZeroFree.IsDescent`, and in general it is a descent on the single runner `x % t`, where the
`r`-th runner collects the quotients of the beads congruent to `r` mod `t`.

Since the bead set is primary, `|λ| = ∑ β - ∑_{j < m} j` is the *definition* of the size rather
than a theorem; what remains is that the truncated subtraction does not truncate, i.e. that
`∑_{j < m} j ≤ ∑ β`, which is `sum_range_card_le_sum`. The resulting additive identity is
`size_beta`, and it is the form used throughout, since it never mentions `ℕ` subtraction.

## Main definitions

* `BeadSet`: a finite set of naturals, read as the first-column hook lengths of a partition.
* `partOfBeads`: the parts of the partition named by a bead set, indexed from `0`.
* `beadSize`: the size of that partition.
* `IsRimHook`: `x` is a bead of `S` that can move `t` places left into an unoccupied slot.
* `rimHookRemoval`: the bead set resulting from that move.
* `rimHookHeight`: the number of beads strictly between the vacated and the occupied slot.
* `runner`: the quotients of the beads congruent to `r` mod `t`.
* `RimHookChain`: reachability by exactly `n` successive removals of rim hooks of length `t`.
* `wt`: the `t`-weight, the greatest number of successive length-`t` removals available.
* `IsTCore`: `S` admits no rim hook of length `t`.

## Main results

* `size_beta`: `beadSize S + ∑_{j < S.card} j = ∑ S`.
* `IsRimHook.beadSize_removal`: a length-`t` removal drops the size by exactly `t`.
* `no_long_chain`: no chain of length-`t` removals is longer than the `t`-weight.
* `runner_rimHookRemoval_of_ne`: runners other than `x % t` are unchanged by a removal at `x`.
* `isDescent_runner_rimHookRemoval`: on the runner `x % t` the removal is a descent.
* `finite_beadSets_card_size`: the `t`-cores of a given cardinality and size are finite in
  number.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- A bead set: a finite set of naturals, standing for the partition whose first-column hook
lengths it is, with `S.card` in the role of the length. -/
@[zf_tag "def_beta"]
abbrev BeadSet := Finset ℕ

/-- The parts of the partition named by a bead set, indexed from `0`: with the beads listed
decreasingly as `s₀ > s₁ > ⋯`, the `i`-th part is `sᵢ - m + i` where `m` is the number of beads.

Written `sᵢ + i + 1 - m` so that the truncated subtraction is the harmless one: for a bead set
of `m` elements the `i`-th largest is at least `m - i - 1`. -/
@[zf_tag "def_part_of_beads"]
def partOfBeads (S : BeadSet) (i : ℕ) : ℕ :=
  ((S.sort (· ≥ ·)).getD i 0) + i + 1 - S.card

/-- The size of the partition named by a bead set; `size_beta` says the subtraction is
honest. -/
def beadSize (S : BeadSet) : ℕ := (∑ x ∈ S, x) - ∑ j ∈ range S.card, j

/-- The size identity, additively: no truncation occurs in `beadSize`, because a set of `k`
distinct naturals has sum at least `0 + 1 + ⋯ + (k - 1)`. -/
@[zf_tag "lem_size_beta"]
theorem size_beta (S : BeadSet) :
    beadSize S + ∑ j ∈ range S.card, j = ∑ x ∈ S, x := by
  have h := sum_range_card_le_sum S
  rw [beadSize]
  omega

/-- A rim hook of length `t`: an admissible bead, one that can move `t` places left into an
unoccupied slot. -/
@[zf_tag "def_rim_hook"]
def IsRimHook (t : ℕ) (S : BeadSet) (x : ℕ) : Prop :=
  x ∈ S ∧ t ≤ x ∧ x - t ∉ S

/-- Removal of a rim hook: the bead moves `t` places left. -/
@[zf_tag "def_rimhook_removal"]
def rimHookRemoval (t : ℕ) (S : BeadSet) (x : ℕ) : BeadSet :=
  insert (x - t) (S.erase x)

/-- The height of a rim hook: the number of beads strictly between the vacated slot and the
occupied one. This is the abacus leg length, and it is what carries the sign in the
Murnaghan–Nakayama recursion. -/
@[zf_tag "def_rimhook_height"]
def rimHookHeight (t : ℕ) (S : BeadSet) (x : ℕ) : ℕ :=
  (S.filter (fun y => x - t < y ∧ y < x)).card

/-- The `r`-th runner: the quotients of the beads congruent to `r` mod `t`. A rim-hook removal
is a descent on exactly one runner. -/
@[zf_tag "def_runner"]
def runner (t r : ℕ) (S : BeadSet) : BeadSet :=
  (S.filter (fun x => x % t = r)).image (fun x => x / t)

variable {t x : ℕ} {S : BeadSet}

/-- A removal preserves the number of beads. -/
theorem IsRimHook.card_removal (h : IsRimHook t S x) :
    (rimHookRemoval t S x).card = S.card := by
  obtain ⟨hxS, htx, hx1⟩ := h
  have hne : x - t ∉ S.erase x := fun hmem => hx1 (mem_of_mem_erase hmem)
  have hpos : 1 ≤ S.card := card_pos.mpr ⟨x, hxS⟩
  rw [rimHookRemoval, card_insert_of_notMem hne, card_erase_of_mem hxS]
  omega

/-- A removal decreases the sum of the beads by exactly `t`, stated additively so that no
truncated subtraction appears. -/
theorem IsRimHook.sum_removal (h : IsRimHook t S x) :
    (∑ y ∈ rimHookRemoval t S x, y) + t = ∑ y ∈ S, y := by
  obtain ⟨hxS, htx, hx1⟩ := h
  have hne : x - t ∉ S.erase x := fun hmem => hx1 (mem_of_mem_erase hmem)
  have hS : x + ∑ y ∈ S.erase x, y = ∑ y ∈ S, y :=
    Finset.add_sum_erase S (fun y => y) hxS
  rw [rimHookRemoval, sum_insert hne]
  omega

/-- Removing a rim hook of length `t` drops the size by exactly `t`. -/
@[zf_tag "lem_removal_size"]
theorem IsRimHook.beadSize_removal (h : IsRimHook t S x) :
    beadSize (rimHookRemoval t S x) + t = beadSize S := by
  have hcard := h.card_removal
  have hsum := h.sum_removal
  have h1 := size_beta S
  have h2 := size_beta (rimHookRemoval t S x)
  rw [hcard] at h2
  omega

open scoped Classical in
/-- `RimHookChain t n S T`: `T` is reached from `S` by exactly `n` successive removals of rim
hooks of length `t`. -/
inductive RimHookChain (t : ℕ) : ℕ → BeadSet → BeadSet → Prop
  | refl (S : BeadSet) : RimHookChain t 0 S S
  | step {n : ℕ} {S T : BeadSet} {x : ℕ} :
      IsRimHook t S x → RimHookChain t n (rimHookRemoval t S x) T →
      RimHookChain t (n + 1) S T

/-- A chain drops the size by `t` per step. -/
theorem RimHookChain.beadSize_add {t n : ℕ} {S T : BeadSet}
    (h : RimHookChain t n S T) : beadSize T + n * t = beadSize S := by
  induction h with
  | refl => simp
  | step hr _ ih =>
    have := hr.beadSize_removal
    rw [← this, ← ih]; ring

open scoped Classical in
/-- The `t`-weight: the greatest number of successive rim-hook removals of length `t` available
from `S`.

`Nat.findGreatest` bounds the search by `beadSize S`, which keeps this a total function;
`no_long_chain` shows the bound is never the binding constraint. -/
@[zf_tag "def_wt"]
noncomputable def wt (t : ℕ) (S : BeadSet) : ℕ :=
  Nat.findGreatest (fun k => ∃ T, RimHookChain t k S T) (beadSize S)

/-- There is no chain of removals longer than the `t`-weight.

CAREFUL — this bounds a *pure* `t`-chain, and nothing more. A Murnaghan–Nakayama expansion
produces chains whose length-`t` removals are *interleaved* with hooks of other lengths, and
`wt t` is not non-increasing under those:

```
S  = {1, 4}, t = 3:  4 ↦ 1 is blocked (1 ∈ S) and 1 ↦ -2 is invalid, so
                     `wt 3 S = 0` — `S` is a 3-core.
remove the 1-hook 1 ↦ 0:     S' = {0, 4}
S' = {0, 4}, t = 3:  4 ↦ 1 is available, since 1 ∉ S'. So `wt 3 S' ≥ 1`.
```

Removing a `1`-hook turns a `3`-core into a non-`3`-core. So a bound on pure `t`-chains does
not bound the number of `t`-removals inside a mixed chain: that needs the parts reordered so
that the `t`-hooks are processed first, which is what `ZeroFree.ChiPerm` provides. -/
@[zf_tag "lem_no_long_chain"]
theorem no_long_chain {t n : ℕ} {S T : BeadSet} (ht : 1 ≤ t)
    (h : RimHookChain t n S T) : n ≤ wt t S := by
  classical
  have hsz := h.beadSize_add
  have hn : n ≤ beadSize S := by nlinarith [Nat.zero_le (beadSize T)]
  exact Nat.le_findGreatest hn ⟨T, h⟩

/-- A bead set is a *`t`-core* when it admits no rim hook of length `t`. -/
@[zf_tag "def_tcore"]
def IsTCore (t : ℕ) (S : BeadSet) : Prop := ∀ x, ¬ IsRimHook t S x

/-- A `t`-core has `t`-weight zero. -/
theorem IsTCore.wt_eq_zero {t : ℕ} {S : BeadSet} (h : IsTCore t S) : wt t S = 0 := by
  classical
  rw [wt, Nat.findGreatest_eq_zero_iff]
  intro k hk _ hP
  obtain ⟨T, hchain⟩ := hP
  cases hchain with
  | refl => omega
  | step hr _ => exact absurd hr (h _)

/-- A `1`-rim hook is exactly a descent. -/
theorem isRimHook_one_iff_isDescent {S T : BeadSet} {x : ℕ} :
    (IsRimHook 1 S x ∧ T = rimHookRemoval 1 S x) ↔
      (x ∈ S ∧ x ≠ 0 ∧ x - 1 ∉ S ∧ T = insert (x - 1) (S.erase x)) := by
  constructor
  · rintro ⟨⟨hxS, h1x, hx1⟩, rfl⟩
    exact ⟨hxS, by omega, hx1, rfl⟩
  · rintro ⟨hxS, hx0, hx1, rfl⟩
    exact ⟨⟨hxS, by omega, hx1⟩, rfl⟩

/-! ### Rim-hook removal acts on one runner only

The runner independence, in both halves: removing a rim hook at `x` leaves every runner other
than `x % t` untouched, and on the runner `x % t` itself the move is exactly a descent.
Together these say a rim-hook removal is one bead moving one place left on one runner, which
is what lets the descent count be applied runner-by-runner. -/

open scoped Classical in
/-- Membership in a runner, unfolded. -/
theorem mem_runner_iff {t r z : ℕ} {S : BeadSet} :
    z ∈ runner t r S ↔ ∃ y ∈ S, y % t = r ∧ y / t = z := by
  simp only [runner, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hyS, hyr⟩, hyz⟩
    exact ⟨y, hyS, hyr, hyz⟩
  · rintro ⟨y, hyS, hyr, hyz⟩
    exact ⟨y, ⟨hyS, hyr⟩, hyz⟩

open scoped Classical in
/-- Runners other than `x % t` are unchanged by removing a rim hook at `x`. -/
theorem runner_rimHookRemoval_of_ne {t x r : ℕ} {S : BeadSet}
    (h : IsRimHook t S x) (hr : r ≠ x % t) :
    runner t r (rimHookRemoval t S x) = runner t r S := by
  obtain ⟨hxS, htx, hx1⟩ := h
  have hxeq : x - t + t = x := Nat.sub_add_cancel htx
  have hxt : (x - t) % t = x % t := by
    conv_rhs => rw [← hxeq]
    rw [Nat.add_mod_right]
  have hfil : (rimHookRemoval t S x).filter (fun y => y % t = r)
      = S.filter (fun y => y % t = r) := by
    ext y
    simp only [rimHookRemoval, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_erase]
    constructor
    · rintro ⟨hy | ⟨hyne, hyS⟩, hyr⟩
      · subst hy
        rw [hxt] at hyr
        exact absurd hyr.symm hr
      · exact ⟨hyS, hyr⟩
    · rintro ⟨hyS, hyr⟩
      refine ⟨Or.inr ⟨?_, hyS⟩, hyr⟩
      rintro rfl
      exact hr hyr.symm
  unfold runner
  rw [hfil]

open scoped Classical in
/-- **On its own runner, a rim-hook removal is a descent.** The complement of
`runner_rimHookRemoval_of_ne`, and with it the full independence statement: a length-`t` rim
hook at `x` moves the bead `x / t` one place left on runner `x % t` and touches nothing else.

The bead that moves is `x / t` and it lands on `x / t - 1`, which is unoccupied precisely
because `x - t ∉ S`: a bead sitting there would have the same residue and the same quotient as
`x - t`, hence *be* `x - t`. That last step is `Nat.ext_div_modEq`, the fibrewise injectivity
of `(· / t)` on a fibre of `(· % t)`. -/
theorem isDescent_runner_rimHookRemoval {t x : ℕ} {S : BeadSet} (ht : 1 ≤ t)
    (h : IsRimHook t S x) :
    IsDescent (runner t (x % t) S) (runner t (x % t) (rimHookRemoval t S x)) := by
  obtain ⟨hxS, htx, hx1⟩ := h
  have hxeq : x - t + t = x := Nat.sub_add_cancel htx
  have hmod : (x - t) % t = x % t := by
    conv_rhs => rw [← hxeq]
    rw [Nat.add_mod_right]
  have hdiv : (x - t) / t + 1 = x / t := by
    conv_rhs => rw [← hxeq]
    rw [Nat.add_div_right _ ht]
  refine ⟨x / t, mem_runner_iff.mpr ⟨x, hxS, rfl, rfl⟩, (Nat.div_pos htx ht).ne', ?_, ?_⟩
  · -- The target slot is empty: a bead there would have to be `x - t` itself.
    intro hmem
    obtain ⟨y, hyS, hyr, hyq⟩ := mem_runner_iff.mp hmem
    have hmodeq : y % t = (x - t) % t := by rw [hyr, hmod]
    have hdvd : y / t = (x - t) / t := by rw [hyq, ← hdiv, Nat.add_sub_cancel]
    exact hx1 (Nat.ext_div_modEq hdvd hmodeq ▸ hyS)
  · ext z
    simp only [mem_runner_iff, rimHookRemoval, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨y, hy | ⟨hyx, hyS⟩, hyr, hyz⟩
      · subst hy
        exact Or.inl (by rw [← hyz, ← hdiv, Nat.add_sub_cancel])
      · refine Or.inr ⟨?_, y, hyS, hyr, hyz⟩
        rintro rfl
        exact hyx (Nat.ext_div_modEq hyz hyr)
    · rintro (rfl | ⟨hz, y, hyS, hyr, hyz⟩)
      · exact ⟨x - t, Or.inl rfl, hmod, by rw [← hdiv, Nat.add_sub_cancel]⟩
      · refine ⟨y, Or.inr ⟨?_, hyS⟩, hyr, hyz⟩
        rintro rfl
        exact hz hyz.symm

/-! ### The bead sets of a given size are a finite family

The size identity bounds every bead of a set with `S.card = m` and `beadSize S = m`, so those
bead sets inject into the powerset of a fixed `range`. Finiteness is what lets `Set.ncard_pos`
turn a positive count of `t`-cores into an actual `t`-core. -/

/-- Every bead of a set with `S.card = m` and `beadSize S = m` is at most `m + ∑_{j < m} j`.

Immediate from `size_beta`, which pins `∑ S = m + ∑_{j < m} j` exactly. -/
theorem le_of_mem_of_beadSize {m : ℕ} {S : BeadSet}
    (hcard : S.card = m) (hsize : beadSize S = m) {x : ℕ} (hx : x ∈ S) :
    x ≤ m + ∑ j ∈ range m, j := by
  have h := size_beta S
  rw [hcard, hsize] at h
  have hle : x ≤ ∑ y ∈ S, y :=
    Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx
  omega

/-- Hence the bead sets of card `m` and size `m` all sit inside one fixed
`range`, so there are finitely many of them. -/
theorem finite_beadSets (m : ℕ) :
    {S : BeadSet | S.card = m ∧ beadSize S = m}.Finite := by
  refine Set.Finite.subset
    (Finset.powerset (range (m + (∑ j ∈ range m, j) + 1))).finite_toSet ?_
  rintro S ⟨hcard, hsize⟩
  simp only [Finset.mem_coe, Finset.mem_powerset]
  intro x hx
  exact mem_range.mpr (by have := le_of_mem_of_beadSize hcard hsize hx; omega)

/-- **The `t`-cores of a given card and size form a finite family.**

`size_beta` pins `∑ S = m + ∑_{j < m} j` once the card and the size are both `m`, so every bead
is bounded by that number and the family injects into the powerset of a `range`. -/
theorem finite_beadSets_card_size (t m : ℕ) :
    {S : BeadSet | S.card = m ∧ beadSize S = m ∧ IsTCore t S}.Finite := by
  classical
  refine Set.Finite.subset
    ((Finset.range (m + (∑ j ∈ range m, j) + 1)).powerset).finite_toSet ?_
  intro S hS
  obtain ⟨hcard, hsize, -⟩ := hS
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro y hy
  rw [mem_range]
  have h1 := size_beta S
  rw [hcard, hsize] at h1
  have h2 : y ≤ ∑ x ∈ S, x := Finset.single_le_sum (fun i _ => Nat.zero_le i) hy
  omega

end ZeroFree
