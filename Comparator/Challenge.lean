/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves.

-/

@[expose] public section

namespace ZeroFree

open Finset

/-! ## The abacus -/

/-- A bead set: a finite set of naturals, standing for the partition whose
first-column hook lengths it is, with `S.card` in the role of the length. -/
abbrev BeadSet := Finset ℕ

/-- The size of the partition named by a bead set. The truncated subtraction never
fires: a set of `m` distinct naturals has sum at least `0 + 1 + ⋯ + (m-1)`. -/
def beadSize (S : BeadSet) : ℕ := (∑ x ∈ S, x) - ∑ j ∈ range S.card, j

/-- A rim hook of length `t`: a bead `x` that can move `t` places left into an
unoccupied slot. All three conjuncts matter, `t ≤ x` being what makes the
subtraction honest. -/
def IsRimHook (t : ℕ) (S : BeadSet) (x : ℕ) : Prop :=
  x ∈ S ∧ t ≤ x ∧ x - t ∉ S

/-- Removal of a rim hook: the bead moves `t` places left. -/
def rimHookRemoval (t : ℕ) (S : BeadSet) (x : ℕ) : BeadSet :=
  insert (x - t) (S.erase x)

/-- The height of a rim hook: the number of beads *strictly* between the vacated
slot and the occupied one. This is the abacus leg length, one less than the rim
hook's vertical span, and it carries the sign in the recursion below. -/
def rimHookHeight (t : ℕ) (S : BeadSet) (x : ℕ) : ℕ :=
  (S.filter (fun y => x - t < y ∧ y < x)).card

/-- A bead set is a *`t`-core* when it admits no rim hook of length `t`. -/
def IsTCore (t : ℕ) (S : BeadSet) : Prop := ∀ x, ¬ IsRimHook t S x

/-! ## The character value

`χ^λ(μ)` is *defined* by the Murnaghan–Nakayama recursion, in its standard abacus
form: there is no `S_n` character theory in Mathlib to define it from. The rule is
Theorem 2.4.7 of James–Kerber, *The Representation Theory of the Symmetric Group*
(Encyclopedia of Mathematics **16**, Addison–Wesley, 1981). -/

/-- The Murnaghan–Nakayama value `χ^S(w)`, by recursion on the list `w` of part
sizes. The filter is the set of rim hooks of length `t` in `S`, the conjunct
`x ∈ S` of `IsRimHook` being supplied by filtering `S` itself.

The value is a priori a function of the *ordering* of `w`, since the recursion
peels off the head; invariance under reordering is a theorem, not a convention. -/
noncomputable def chi (S : BeadSet) : List ℕ → ℤ
  | [] => if beadSize S = 0 then 1 else 0
  | t :: v =>
      ∑ x ∈ S.filter (fun x => t ≤ x ∧ x - t ∉ S),
        (-1) ^ (rimHookHeight t S x) * chi (rimHookRemoval t S x) v

/-! ## Zero-free columns -/

/-- A column of the character table is *zero-free* when no row gives the value `0`.

Rows are the bead sets of card `n` and size `n`. This is a normalization, not a
restriction: a partition of `n` has at most `n` parts, so every partition of `n`
is represented at card `n`, and exactly once. -/
def ZeroFreeColumn (n : ℕ) (μ : Nat.Partition n) : Prop :=
  ∀ S : BeadSet, S.card = n → beadSize S = n → chi S μ.parts.toList ≠ 0

open scoped Classical in
/-- `D n`, the number of zero-free columns of the character table of `S n`. -/
noncomputable def D (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun μ : Nat.Partition n => ZeroFreeColumn n μ)).card

/-! ## The sieve vocabulary -/

/-- A natural number is *Loeschian* when it is a positive value of the Eisenstein
norm form `x² + xy + y²`, with `x` and `y` ranging over all of `ℤ`. -/
def Loeschian (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ x y : ℤ, (m : ℤ) = x ^ 2 + x * y + y ^ 2

/-- A set of positive integers is *multiplicative* when membership is determined by
coprime factorisations in both directions. -/
def IsMultiplicativeSet (N : Set ℕ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → (m * n ∈ N ↔ m ∈ N ∧ n ∈ N)

open scoped Classical in
/-- The sieve density `δ(N; X) = ∏_{p ≤ X, p ∉ N} (1 - 1/p)`. -/
noncomputable def sieveDensity (N : Set ℕ) (X : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∉ N),
    (1 - 1 / (p : ℝ))

/-- `∑_{p ≤ X, p ≡ a mod q} 1/p`. -/
noncomputable def primeRecipSumMod (X : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p % q = a % q),
    (1 / (p : ℝ))

/-- `∑_{p ≤ X} 1/p`. -/
noncomputable def primeRecipSum (X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p), (1 / (p : ℝ))

/-- `∑_{w < p ≤ z, p ≡ a mod q} 1/p`, as a difference of prefix sums. -/
noncomputable def primeRecipSumModIoc (w z : ℝ) (q a : ℕ) : ℝ :=
  primeRecipSumMod z q a - primeRecipSumMod w q a

/-- `∑_{w < p ≤ z} 1/p`, as a difference of prefix sums. -/
noncomputable def primeRecipSumIoc (w z : ℝ) : ℝ :=
  primeRecipSum z - primeRecipSum w

open scoped Classical in
/-- `∑_{p ≤ X, p ∈ N} 1/p`. -/
noncomputable def primeRecipSumMem (X : ℝ) (N : Set ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∈ N),
    (1 / (p : ℝ))

/-- `∑_{w < p ≤ z, p ∈ N} 1/p`, as a difference of prefix sums. -/
noncomputable def primeRecipSumMemIoc (w z : ℝ) (N : Set ℕ) : ℝ :=
  primeRecipSumMem z N - primeRecipSumMem w N

/-! ## The external inputs as hypotheses

The six statements below are what the source paper cites rather than proves. Both
theorems at the end of this file assume them; the paper's own theorems do not.
`LiteratureInputs` is not known to be nonempty, so a field stated more strongly
than its citation supports would make both theorems vacuously provable, and each
therefore carries the source it is to be read against. -/

/-- The six statements this development borrows from the literature. Every field is
*assumed* and none is proved anywhere in the development. -/
structure LiteratureInputs where
  /-- **Representation by the Eisenstein norm form.** A positive integer is of the
  form `x² + xy + y²` exactly when every prime `p ≡ 2 mod 3` divides it to even
  exponent.

  P. Marshall, *The Loeschian numbers as a problem in number theory*. -/
  eisenstein_criterion :
    ∀ m : ℕ, 1 ≤ m →
      (Loeschian m ↔ ∀ p : ℕ, p.Prime → p % 3 = 2 → Even (m.factorization p))
  /-- **Mertens' theorem for arithmetic progressions, asymptotic form.**

  K. S. Williams, *Mertens' theorem for arithmetic progressions*, J. Number Theory
  **6** (1974) 353–359, doi 10.1016/0022-314X(74)90032-8. -/
  mertens_ap :
    ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
        |primeRecipSumMod X q a - (1 / (q.totient : ℝ)) * Real.log (Real.log X)| ≤ K
  /-- **Mertens' theorem for arithmetic progressions, uniform form.**

  Williams, as above. A separate field on purpose: the two forms are not
  equivalent, and deriving either from the other is not work the paper does. -/
  mertens_ap_uniform :
    ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ∃ K : ℝ, 0 < K ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        |primeRecipSumModIoc w z q a
          - (1 / (q.totient : ℝ)) * primeRecipSumIoc w z| ≤ K / Real.log w
  /-- **Positivity of `t`-cores for `t ≥ 4`.** Every natural number is the size of at
  least one `t`-core, on bead sets of card `m`.

  A. Granville and K. Ono, Trans. Amer. Math. Soc. **348** (1996) 331–347, doi
  10.1090/S0002-9947-96-01481-X; K. Ono, Acta Arith. **66** (1994) 221–228. -/
  tcore_positivity :
    ∀ t : ℕ, 4 ≤ t → ∀ m : ℕ,
      ∃ S : BeadSet, S.card = m ∧ beadSize S = m ∧ IsTCore t S
  /-- **The `3`-core count.** `c₃(m) = ∑_{d ∣ 3m+1} (d/3)`, with `(·/3)` the
  quadratic character mod `3`. Assumed as the formula only; the multiplicativity
  argument turning it into the `3`-core criterion is proved in the development.

  Granville and Ono, as above. -/
  three_core_count :
    ∀ m : ℕ,
      {S : BeadSet | S.card = m ∧ beadSize S = m ∧ IsTCore 3 S}.ncard
        = ∑ d ∈ (3 * m + 1).divisors, legendreSym 3 (d : ℤ)
  /-- **The Matomäki–Radziwiłł gap theorem**, in the source paper's restated form
  rather than the cited corollary raw. The enumeration of `N` is `Nat.nth`; note
  `1 ≤ γ` closed and `γ < 3/2` open.

  K. Matomäki and M. Radziwiłł, *Multiplicative functions in short intervals II*,
  arXiv:1007.5310, Corollary 1.2(ii). -/
  mr_gap :
    ∀ N : Set ℕ, IsMultiplicativeSet N → ∀ α : ℝ, 0 < α → ∀ K : ℝ, 0 < K →
      (∀ w z : ℝ, 2 ≤ w → w ≤ z →
        α * primeRecipSumIoc w z - K / Real.log w
          ≤ primeRecipSumMemIoc w z N) →
      ∀ γ : ℝ, 1 ≤ γ → γ < 3 / 2 →
        ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
          ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
              (fun i => (Nat.nth (· ∈ N) i : ℝ) ≤ X),
            ((Nat.nth (· ∈ N) (i + 1) - Nat.nth (· ∈ N) i : ℝ)) ^ γ
          ≤ C * X * sieveDensity N X ^ (1 - γ)

end ZeroFree

namespace ZeroFree.Challenge

/-- **`thm_pointwise` — the pointwise bound.** `D(n) ≤ C n^{3/4}` for every `n ≥ 1`,
with a single constant `C` quantified outside `n`. The exponent is `Real.rpow`. -/
theorem thm_pointwise (L : LiteratureInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (D n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 4) :=
  sorry

/-- **`thm_almostall` — the almost-all bound.** For `B > 5/6` some `C_B > 0` has:
for every `ε > 0` there is a `C > 0` with

    #{ 1 ≤ n ≤ X : D(n) > C_B n^{1/2} (log n)^B } ≤ C X (log X)^{-(1/2)(B-5/6)+ε}

for every `X ≥ 3`. `C_B` is chosen *before* `ε`, so the threshold is a fixed one. -/
theorem thm_almostall (L : LiteratureInputs) {B : ℝ} (hB : 5 / 6 < B) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter
          (fun n : ℕ => CB * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ^ B
            < (D n : ℝ))).card : ℝ)
        ≤ C * X * Real.log X ^ (-(1 / 2 : ℝ) * (B - 5 / 6) + ε) :=
  sorry

end ZeroFree.Challenge
