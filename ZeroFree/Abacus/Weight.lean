/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZeroFree.Abacus.Beads
public import ZeroFree.Meta.Attr

/-!
# The `t`-weight is the total bead displacement

`wt t S = ∑_{r < t} (∑ Q_r - ∑_{j < |Q_r|} j)` where `Q_r = runner t r S`. This turns the
`Nat.findGreatest` over chains defining `wt` into a closed formula, one summand per runner. Each
summand is the descent count of `ZeroFree.Abacus.Descent`, already proved exact there, so the
content here is precisely the *independence* of the runners: a chain of rim-hook removals is a
choice, for each `r`, of a chain of descents of `Q_r`, interleaved in some order.

The independence is not used as a bijection between chains — that would force reasoning about
interleavings. Instead the whole argument runs through one conservation law: `totalDisp` drops
by **exactly one** per rim-hook removal (`totalDisp_removal`). That single step gives both
halves. The upper bound is induction along a chain. Attainment is induction on `totalDisp`
itself: while it is positive some runner still has a descent, which is a rim hook
(`exists_rimHook_of_descent`), so the chain can be extended. Interleaving never appears, because
the order the runners are drained in is irrelevant to a quantity that only ever decreases by
one.

The two correspondences this rests on live in `ZeroFree.Abacus.Beads`:
`isDescent_runner_rimHookRemoval` (a removal is a descent on its own runner) and
`runner_rimHookRemoval_of_ne` (the other runners are untouched). The converse direction — every
descent of a runner comes from a rim hook — is `exists_rimHook_of_descent` below, and it is what
makes `totalDisp = 0` equivalent to being a `t`-core rather than merely implied by it.

## Main definitions

* `runnerDisp`: the number of bead moves one runner still admits.
* `totalDisp`: the sum of `runnerDisp` over the `t` runners.
* `extendTop`: the bead set with its largest bead pushed up by `s` full periods.

## Main results

* `exists_rimHook_of_descent`: every descent of a runner comes from a rim hook.
* `totalDisp_removal`: a rim-hook removal drops the total displacement by exactly one.
* `totalDisp_eq_zero_of_isTCore`: a `t`-core has zero total displacement.
* `exists_rimHookChain_totalDisp`: a chain of removals of length exactly `totalDisp t S`.
* `wt_eq_totalDisp`: the `t`-weight is the total displacement.
* `totalDisp_extendTop`: a first-row extension by `s` periods raises the displacement by `s`.
* `wt_extendTop`: a first-row extension of a `t`-core by `s` periods has `t`-weight `s`.
-/

@[expose] public section

namespace ZeroFree

open Finset

/-- The displacement of one runner: how many bead moves it still admits. -/
def runnerDisp (t r : ℕ) (S : BeadSet) : ℕ :=
  (∑ x ∈ runner t r S, x) - ∑ j ∈ range (runner t r S).card, j

/-- The total displacement, summed over the `t` runners. -/
def totalDisp (t : ℕ) (S : BeadSet) : ℕ :=
  ∑ r ∈ range t, runnerDisp t r S

/-- A descent drops a set's displacement by exactly one, stated additively. -/
theorem disp_of_isDescent {P Q : Finset ℕ} (h : IsDescent P Q) :
    ((∑ y ∈ Q, y) - ∑ j ∈ range Q.card, j) + 1
      = (∑ y ∈ P, y) - ∑ j ∈ range P.card, j := by
  have hsum := h.sum_succ
  have hcard := h.card_eq
  have hlowP := sum_range_card_le_sum P
  have hlowQ := sum_range_card_le_sum Q
  rw [hcard] at hlowQ ⊢
  omega

/-- **Every descent of a runner comes from a rim hook.** The converse of
`isDescent_runner_rimHookRemoval`, and the direction that makes a zero total displacement
*equivalent* to being a `t`-core.

The bead is recovered from its runner position by `x = t q + r`: the residue and the quotient
together determine the bead. -/
theorem exists_rimHook_of_descent {t r q : ℕ} {S : BeadSet} (ht : 1 ≤ t) (hr : r < t)
    (hq : q ∈ runner t r S) (hq0 : q ≠ 0) (hq1 : q - 1 ∉ runner t r S) :
    IsRimHook t S (t * q + r) := by
  have hmod : (t * q + r) % t = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hdiv : (t * q + r) / t = q := by
    rw [Nat.mul_add_div ht, Nat.div_eq_of_lt hr, Nat.add_zero]
  obtain ⟨y, hyS, hyr, hyq⟩ := mem_runner_iff.mp hq
  have hyx : y = t * q + r := by
    refine Nat.ext_div_modEq (n := t) ?_ ?_
    · rw [hyq, hdiv]
    · change y % t = (t * q + r) % t
      rw [hyr, hmod]
  refine ⟨hyx ▸ hyS, ?_, ?_⟩
  · -- `q ≥ 1` puts the bead at least `t` places along.
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * q := Nat.mul_le_mul_left t this
      _ ≤ t * q + r := Nat.le_add_right _ _
  · -- A bead in the target slot would put `q - 1` on the runner.
    intro hmem
    refine hq1 (mem_runner_iff.mpr ⟨t * q + r - t, hmem, ?_, ?_⟩)
    · have hle : t ≤ t * q + r := by
        have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        calc t = t * 1 := (Nat.mul_one t).symm
          _ ≤ t * q := Nat.mul_le_mul_left t this
          _ ≤ t * q + r := Nat.le_add_right _ _
      conv_rhs => rw [← hmod]
      conv_rhs => rw [← Nat.sub_add_cancel hle]
      rw [Nat.add_mod_right]
    · have hle : t ≤ t * q + r := by
        have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        calc t = t * 1 := (Nat.mul_one t).symm
          _ ≤ t * q := Nat.mul_le_mul_left t this
          _ ≤ t * q + r := Nat.le_add_right _ _
      have hstep : (t * q + r - t) / t + 1 = (t * q + r) / t := by
        conv_rhs => rw [← Nat.sub_add_cancel hle]
        rw [Nat.add_div_right _ ht]
      rw [hdiv] at hstep
      omega

/-- **The conservation law.** Removing a rim hook of length `t` drops the total displacement by
exactly one.

This is where the runner independence is spent: the runner `x % t` contributes the `1` via
`disp_of_isDescent`, and every other runner contributes `0` because
`runner_rimHookRemoval_of_ne` says it is literally unchanged. -/
theorem totalDisp_removal {t x : ℕ} {S : BeadSet} (ht : 1 ≤ t)
    (h : IsRimHook t S x) :
    totalDisp t (rimHookRemoval t S x) + 1 = totalDisp t S := by
  classical
  have hmem : x % t ∈ range t := mem_range.mpr (Nat.mod_lt _ ht)
  have hsplit : ∀ T : BeadSet, totalDisp t T
      = runnerDisp t (x % t) T + ∑ r ∈ (range t).erase (x % t), runnerDisp t r T := by
    intro T
    rw [totalDisp, ← Finset.add_sum_erase _ (fun r => runnerDisp t r T) hmem]
  have hrest : ∑ r ∈ (range t).erase (x % t), runnerDisp t r (rimHookRemoval t S x)
      = ∑ r ∈ (range t).erase (x % t), runnerDisp t r S := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hne : r ≠ x % t := (Finset.mem_erase.mp hr).1
    rw [runnerDisp, runnerDisp, runner_rimHookRemoval_of_ne h hne]
  have hone : runnerDisp t (x % t) (rimHookRemoval t S x) + 1
      = runnerDisp t (x % t) S :=
    disp_of_isDescent (isDescent_runner_rimHookRemoval ht h)
  rw [hsplit (rimHookRemoval t S x), hsplit S, hrest]
  omega

/-- A `t`-core has zero total displacement: no runner admits a descent, so each
is an initial segment. -/
theorem totalDisp_eq_zero_of_isTCore {t : ℕ} {S : BeadSet} (ht : 1 ≤ t)
    (h : IsTCore t S) : totalDisp t S = 0 := by
  classical
  rw [totalDisp, Finset.sum_eq_zero]
  intro r hr
  have hrt : r < t := mem_range.mp hr
  have hnd : ∀ Q, ¬ IsDescent (runner t r S) Q := by
    rintro Q ⟨q, hqmem, hq0, hq1, -⟩
    exact h _ (exists_rimHook_of_descent ht hrt hqmem hq0 hq1)
  have hrange := eq_range_of_no_descent hnd
  rw [runnerDisp]
  conv_lhs => rw [hrange]
  rw [card_range]
  omega

/-- Contrapositive of `totalDisp_eq_zero_of_isTCore`: a positive total
displacement exhibits a rim hook. This is what drives the attainment induction. -/
theorem exists_rimHook_of_totalDisp_pos {t : ℕ} {S : BeadSet} (ht : 1 ≤ t)
    (h : 0 < totalDisp t S) : ∃ x, IsRimHook t S x := by
  by_contra hc
  push Not at hc
  have hz := totalDisp_eq_zero_of_isTCore ht hc
  omega

/-- **Attainment.** There is a chain of rim-hook removals from `S` of length exactly
`totalDisp t S`.

Induction on the displacement, which `totalDisp_removal` makes legitimate: each step of the
chain decreases it by one, so the recursion is well-founded on a quantity that is visibly
decreasing. Interleaving of the runners never arises. -/
theorem exists_rimHookChain_totalDisp {t : ℕ} (ht : 1 ≤ t) :
    ∀ d : ℕ, ∀ S : BeadSet, totalDisp t S = d →
      ∃ T, RimHookChain t (totalDisp t S) S T := by
  intro d
  induction d with
  | zero =>
    intro S hS
    exact ⟨S, by rw [hS]; exact RimHookChain.refl S⟩
  | succ n ih =>
    intro S hS
    have hpos : 0 < totalDisp t S := by omega
    obtain ⟨x, hx⟩ := exists_rimHook_of_totalDisp_pos ht hpos
    have hstep := totalDisp_removal ht hx
    have hrec : totalDisp t (rimHookRemoval t S x) = n := by omega
    obtain ⟨T, hT⟩ := ih (rimHookRemoval t S x) hrec
    rw [hrec] at hT
    exact ⟨T, by rw [hS]; exact RimHookChain.step hx hT⟩

/-- **Upper bound.** No chain of rim-hook removals is longer than the total displacement. The
same conservation law, run the other way. -/
theorem RimHookChain.le_totalDisp {t n : ℕ} {S T : BeadSet} (ht : 1 ≤ t)
    (h : RimHookChain t n S T) : n ≤ totalDisp t S := by
  induction h with
  | refl => exact Nat.zero_le _
  | step hr _ ih =>
    have := totalDisp_removal ht hr
    omega

/-- A chain of rim-hook removals from `S` of length exactly `wt t S`.

The `Nat.findGreatest` cap at `beadSize S` in the definition of `wt` is not active, and that is
proved here rather than assumed: the attained chain has length `totalDisp t S` and drops the
size by `t ≥ 1` per step, so `totalDisp t S ≤ beadSize S`. -/
theorem exists_rimHookChain_wt {t : ℕ} (ht : 1 ≤ t) (S : BeadSet) :
    ∃ T, RimHookChain t (wt t S) S T := by
  classical
  obtain ⟨T, hT⟩ := exists_rimHookChain_totalDisp ht (totalDisp t S) S rfl
  have hsize := hT.beadSize_add
  have hcap : totalDisp t S ≤ beadSize S := by nlinarith [Nat.zero_le (beadSize T)]
  exact Nat.findGreatest_spec (P := fun k => ∃ U, RimHookChain t k S U) hcap ⟨T, hT⟩

/-! ### First-row extension

In the bead picture, adding `s * t` to `λ₁` is: the *largest* bead `M` moves up by `s * t`. It
keeps its residue, so it stays on its own runner and advances `s` places along it; every other
runner is untouched. So the total displacement rises by exactly `s`, and since a `t`-core has
displacement `0`, the extension has weight `s`.

`M` maximal is not decoration. It is what makes the arriving slot `M / t + s` free, and it is
true of the intended input: the first-column hook lengths of a partition are `λᵢ + m - i`,
largest at `i = 1`. -/

/-- The extended bead set: the largest bead `M` pushed up by `s` full periods. -/
def extendTop (t s M : ℕ) (S : BeadSet) : BeadSet :=
  insert (M + s * t) (S.erase M)

variable {t s M : ℕ} {S : BeadSet}

/-- Pushing a bead up by a multiple of `t` keeps its residue. -/
theorem extend_mod (t s M : ℕ) : (M + s * t) % t = M % t :=
  Nat.add_mul_mod_self_right M s t

/-- ...and advances its runner position by exactly `s`. -/
theorem extend_div (ht : 1 ≤ t) (s M : ℕ) : (M + s * t) / t = M / t + s :=
  Nat.add_mul_div_right _ _ ht

/-- The arriving bead is genuinely new. For `s = 0` it is the departing bead, which `erase`
already removed; for `s ≥ 1` it overshoots the maximum. -/
theorem extend_notMem (hmax : ∀ y ∈ S, y ≤ M) :
    M + s * t ∉ S.erase M := by
  intro hmem
  obtain ⟨hne, hS⟩ := Finset.mem_erase.mp hmem
  have := hmax _ hS
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact hne (by omega)
  · rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact hne (by omega)
    · have : 1 * 1 ≤ s * t := Nat.mul_le_mul hs htp
      omega

/-- Runners other than the moving bead's are untouched by the extension.

Needs no hypothesis on `t`, `M` or `S`: the arriving bead and the departing one both have
residue `M % t`, so a runner at any other residue never sees either. -/
theorem runner_extendTop_of_ne {r : ℕ} (hr : r ≠ M % t) :
    runner t r (extendTop t s M S) = runner t r S := by
  classical
  ext z
  simp only [mem_runner_iff, extendTop, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨y, hy | ⟨-, hyS⟩, hyr, hyz⟩
    · exact absurd (by rw [← hyr, hy, extend_mod]) hr
    · exact ⟨y, hyS, hyr, hyz⟩
  · rintro ⟨y, hyS, hyr, hyz⟩
    refine ⟨y, Or.inr ⟨?_, hyS⟩, hyr, hyz⟩
    rintro rfl
    exact hr hyr.symm

/-- On the moving bead's own runner, the extension advances one position by `s`. -/
theorem runner_extendTop_self (ht : 1 ≤ t) (hM : M ∈ S) (hmax : ∀ y ∈ S, y ≤ M) :
    runner t (M % t) (extendTop t s M S)
      = insert (M / t + s) ((runner t (M % t) S).erase (M / t)) := by
  classical
  ext z
  simp only [mem_runner_iff, extendTop, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨y, hy | ⟨hyM, hyS⟩, hyr, hyz⟩
    · subst hy
      exact Or.inl (by rw [← hyz, extend_div ht])
    · refine Or.inr ⟨?_, y, hyS, hyr, hyz⟩
      rintro rfl
      exact hyM (Nat.ext_div_modEq hyz hyr)
  · rintro (rfl | ⟨hz, y, hyS, hyr, hyz⟩)
    · exact ⟨M + s * t, Or.inl rfl, extend_mod t s M, extend_div ht s M⟩
    · refine ⟨y, Or.inr ⟨?_, hyS⟩, hyr, hyz⟩
      rintro rfl
      exact hz hyz.symm

/-- The moving runner's displacement rises by exactly `s` and every other runner's is
unchanged, so the total rises by `s`. -/
theorem totalDisp_extendTop (ht : 1 ≤ t) (hM : M ∈ S) (hmax : ∀ y ∈ S, y ≤ M) :
    totalDisp t (extendTop t s M S) = totalDisp t S + s := by
  classical
  have hmem : M % t ∈ range t := mem_range.mpr (Nat.mod_lt _ ht)
  have hsplit : ∀ T : BeadSet, totalDisp t T
      = runnerDisp t (M % t) T + ∑ r ∈ (range t).erase (M % t), runnerDisp t r T := by
    intro T
    rw [totalDisp, ← Finset.add_sum_erase _ (fun r => runnerDisp t r T) hmem]
  have hrest : ∑ r ∈ (range t).erase (M % t), runnerDisp t r (extendTop t s M S)
      = ∑ r ∈ (range t).erase (M % t), runnerDisp t r S := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [runnerDisp, runnerDisp,
      runner_extendTop_of_ne (Finset.mem_erase.mp hr).1]
  have hq : M / t ∈ runner t (M % t) S := mem_runner_iff.mpr ⟨M, hM, rfl, rfl⟩
  have hfree : M / t + s ∉ (runner t (M % t) S).erase (M / t) := by
    intro hmem'
    obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hmem'
    obtain ⟨y, hyS, -, hyz⟩ := mem_runner_iff.mp hin
    have hle : y ≤ M := hmax _ hyS
    have : y / t ≤ M / t := Nat.div_le_div_right hle
    omega
  have hcard : (runner t (M % t) (extendTop t s M S)).card
      = (runner t (M % t) S).card := by
    rw [runner_extendTop_self ht hM hmax, Finset.card_insert_of_notMem hfree,
      Finset.card_erase_of_mem hq]
    have : 1 ≤ (runner t (M % t) S).card := Finset.card_pos.mpr ⟨_, hq⟩
    omega
  have hsum : (∑ z ∈ runner t (M % t) (extendTop t s M S), z)
      = (∑ z ∈ runner t (M % t) S, z) + s := by
    rw [runner_extendTop_self ht hM hmax, Finset.sum_insert hfree]
    have := Finset.add_sum_erase (runner t (M % t) S) (fun y => y) hq
    omega
  have hone : runnerDisp t (M % t) (extendTop t s M S)
      = runnerDisp t (M % t) S + s := by
    have hlow := sum_range_card_le_sum (runner t (M % t) S)
    rw [runnerDisp, runnerDisp, hcard, hsum]
    omega
  rw [hsplit (extendTop t s M S), hsplit S, hrest, hone]
  omega

/-- **The `t`-weight is the total bead displacement.** -/
@[zf_tag "lem_wt_beta"]
theorem wt_eq_totalDisp {t : ℕ} (ht : 1 ≤ t) (S : BeadSet) :
    wt t S = totalDisp t S := by
  classical
  obtain ⟨T, hT⟩ := exists_rimHookChain_totalDisp ht (totalDisp t S) S rfl
  have hsize := hT.beadSize_add
  have hcap : totalDisp t S ≤ beadSize S := by nlinarith [Nat.zero_le (beadSize T)]
  refine le_antisymm ?_ (Nat.le_findGreatest hcap ⟨T, hT⟩)
  obtain ⟨U, hU⟩ := exists_rimHookChain_wt ht S
  exact hU.le_totalDisp ht

/-- **A first-row extension of a `t`-core by `s` periods has `t`-weight exactly `s`.**

Proved through `wt_eq_totalDisp`: the extension's displacement is `s` by `totalDisp_extendTop`,
and a `t`-core's is `0`. -/
@[zf_tag "lem_wt_extend"]
theorem wt_extendTop (ht : 1 ≤ t) (hS : IsTCore t S) (hM : M ∈ S)
    (hmax : ∀ y ∈ S, y ≤ M) :
    wt t (extendTop t s M S) = s := by
  rw [wt_eq_totalDisp ht, totalDisp_extendTop ht hM hmax,
    totalDisp_eq_zero_of_isTCore ht hS, Nat.zero_add]

end ZeroFree
