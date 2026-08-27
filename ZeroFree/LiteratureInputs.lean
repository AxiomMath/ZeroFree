/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import ZeroFree.Arithmetic.Basic
public import ZeroFree.Abacus.Beads
public import ZeroFree.Sieve.Basic
public import ZeroFree.Meta.Attr

/-!
# The admitted literature inputs, as a structure of hypotheses

Each field of `LiteratureInputs` is a statement the source paper cites to prior literature: an
Eisenstein-form representation criterion, two forms of Mertens' theorem for arithmetic
progressions, positivity of `t`-cores, the `3`-core count, and the Matomäki–Radziwiłł gap theorem.
None is proved here, and none is a global `axiom` — every theorem resting on one takes a
`LiteratureInputs` argument, so the dependence appears in its type and `#print axioms` stays clean.

`LiteratureInputs` cannot be shown nonempty, `mr_gap` alone putting that out of reach, so a field
stated more strongly than its citation supports would go undetected by any mechanical check. Each
field is therefore stated in the shape its *source* states, not the shape its consumers want, and
its docstring records the citation it is to be read against.

## Main definitions

* `LiteratureInputs`: the admitted statements, bundled as a structure of hypotheses.
* `primeRecipSum`, `primeRecipSumMod`, `primeRecipSumMem`: the sums `∑ 1/p` over the primes
  `p ≤ X`, over those in a fixed residue class, and over those lying in a given set.
* `primeRecipSumIoc`, `primeRecipSumModIoc`, `primeRecipSumMemIoc`: the same sums over `w < p ≤ z`,
  as differences of prefix sums.
-/

@[expose] public section

namespace ZeroFree


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

/-- The statements this development borrows from the literature, bundled so they can be threaded
as a single explicit hypothesis. Every field is *assumed*, and its docstring carries the citation
it is to be read against. -/
structure LiteratureInputs where
  /-- **Representation by the Eisenstein norm form.** A positive integer is of the form
  `x^2 + xy + y^2` exactly when every prime `p ≡ 2 mod 3` divides it to even exponent.

  Marshall, *The Loeschian numbers as a problem in number theory*. -/
  eisenstein_criterion :
    ∀ m : ℕ, 1 ≤ m →
      (Loeschian m ↔ ∀ p : ℕ, p.Prime → p % 3 = 2 → Even (m.factorization p))
  /-- **Mertens' theorem for arithmetic progressions, asymptotic form.** For `a` coprime to `q`,
  `∑_{p ≤ X, p ≡ a mod q} 1/p = (1/φ(q)) log log X + O(1)`.

  Williams, *Mertens' theorem for arithmetic progressions*. -/
  mertens_ap :
    ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
        |primeRecipSumMod X q a - (1 / (q.totient : ℝ)) * Real.log (Real.log X)| ≤ K
  /-- **Mertens' theorem for arithmetic progressions, uniform form.** For `a` coprime to `q` and
  `2 ≤ w ≤ z`, `∑_{w < p ≤ z, p ≡ a mod q} 1/p = (1/φ(q)) ∑_{w < p ≤ z} 1/p + O(1/log w)`.

  Williams, as above. A **separate field on purpose**: the paper uses both forms, they are not
  equivalent, and deriving either from the other is not work the paper does. -/
  mertens_ap_uniform :
    ∀ q a : ℕ, 1 ≤ q → Nat.Coprime a q →
      ∃ K : ℝ, 0 < K ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        |primeRecipSumModIoc w z q a
          - (1 / (q.totient : ℝ)) * primeRecipSumIoc w z| ≤ K / Real.log w
  /-- **Positivity of `t`-cores for `t ≥ 4`.** Every nonnegative integer is the size of at least
  one `t`-core.

  Granville–Ono, *Defect zero p-blocks for finite simple groups*, and Ono, *On the positivity of
  the number of t-core partitions*. The proof goes through modular forms.

  Stated on bead sets of card `m`: a partition of `m` has at most `m` parts, so pinning the card
  represents every one of them exactly once. -/
  tcore_positivity :
    ∀ t : ℕ, 4 ≤ t → ∀ m : ℕ,
      ∃ S : BeadSet, S.card = m ∧ beadSize S = m ∧ IsTCore t S
  /-- **The `3`-core count.** `c₃(m) = ∑_{d ∣ 3m+1} (d/3)`, where `(·/3)` is the quadratic
  character modulo `3`.

  Granville–Ono, *Defect zero p-blocks for finite simple groups*. A generating-function identity.

  Stated with Mathlib's `legendreSym 3` rather than a hand-rolled function taking values in
  `{0, 1, -1}` on residues: the character has to be *completely multiplicative* for the divisor sum
  to be multiplicative in `3m + 1`, which is `legendreSym.mul`. A bespoke copy would force
  re-proving that, and would be a second character in the world for the statement to be about.

  **The count is over bead sets with the card pinned**, matching `tcore_positivity` and
  `ZeroFreeColumn`: a partition of `m` has at most `m` parts, so pinning `S.card = m` represents
  every partition of `m` exactly once, and the bead-set count therefore equals the partition count.
  It is *not* a truncation.

  `Set.ncard` rather than a `Finset.card` over some `powersetCard` bound: the set is finite
  (`size_beta` forces `∑ S = m + ∑_{j<m} j`, so every bead is bounded), but choosing and justifying
  an explicit enclosing range is no part of what Granville–Ono asserts. Baking a bound in would
  state something about a truncated family while claiming the theorem about the real one. -/
  three_core_count :
    ∀ m : ℕ,
      {S : BeadSet | S.card = m ∧ beadSize S = m ∧ IsTCore 3 S}.ncard
        = ∑ d ∈ (3 * m + 1).divisors, legendreSym 3 (d : ℤ)
  /-- **The Matomäki–Radziwiłł gap theorem.** Let `N` be a multiplicative set whose primes carry at
  least an `α`-fraction of the prime reciprocal mass of every range `w < p ≤ z`, up to `K/log w`.
  Then for `1 ≤ γ < 3/2` the `γ`-th moment of the consecutive gaps of `N` below `X` is
  `O(X * sieveDensity N X ^ (1 - γ))`.

  Matomäki–Radziwiłł, *Multiplicative functions in short intervals II*, Corollary 1.2(ii) — stated
  here in **the paper's restated form**, not as the cited corollary verbatim. The paper's passage
  from the corollary to that form is a restatement rather than a proof, so what is assumed is its
  output.

  The enumeration of `N` is `Nat.nth (· ∈ N)`, the increasing enumeration when `N` is infinite. -/
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

/-! ### The admitted inputs, as standalone statements

Nothing in this section is proved: each statement below is a projection of an assumed field of
`LiteratureInputs`, with its arguments implicit and its hypotheses positional. -/

/-- A positive integer is Loeschian exactly when every prime `p ≡ 2 mod 3` divides it to even
exponent. -/
@[zf_tag "lem_eisenstein_criterion"]
theorem LiteratureInputs.eisenstein (L : LiteratureInputs) {m : ℕ} (hm : 1 ≤ m) :
    Loeschian m ↔ ∀ p : ℕ, p.Prime → p % 3 = 2 → Even (m.factorization p) :=
  L.eisenstein_criterion m hm

/-- Mertens' theorem for arithmetic progressions, asymptotic form:
`∑_{p ≤ X, p ≡ a mod q} 1/p = (1/φ(q)) log log X + O(1)`. -/
@[zf_tag "lem_mertens_ap"]
theorem LiteratureInputs.mertens (L : LiteratureInputs) {q a : ℕ} (hq : 1 ≤ q)
    (ha : Nat.Coprime a q) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
      |primeRecipSumMod X q a - (1 / (q.totient : ℝ)) * Real.log (Real.log X)| ≤ K :=
  L.mertens_ap q a hq ha

/-- Mertens' theorem for arithmetic progressions, uniform form: for `2 ≤ w ≤ z`,
`∑_{w < p ≤ z, p ≡ a mod q} 1/p = (1/φ(q)) ∑_{w < p ≤ z} 1/p + O(1/log w)`. -/
@[zf_tag "lem_mertens_ap_uniform"]
theorem LiteratureInputs.mertensUniform (L : LiteratureInputs) {q a : ℕ} (hq : 1 ≤ q)
    (ha : Nat.Coprime a q) :
    ∃ K : ℝ, 0 < K ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      |primeRecipSumModIoc w z q a
        - (1 / (q.totient : ℝ)) * primeRecipSumIoc w z| ≤ K / Real.log w :=
  L.mertens_ap_uniform q a hq ha

/-- For `t ≥ 4`, every natural number is the size of some `t`-core. -/
@[zf_tag "prop_tcore_positivity"]
theorem LiteratureInputs.tcorePositivity (L : LiteratureInputs) {t : ℕ} (ht : 4 ≤ t)
    (m : ℕ) : ∃ S : BeadSet, S.card = m ∧ beadSize S = m ∧ IsTCore t S :=
  L.tcore_positivity t ht m

/-- The number of `3`-cores of size `m` is `∑_{d ∣ 3m+1} (d/3)`. -/
@[zf_tag "lem_three_core_count"]
theorem LiteratureInputs.threeCoreCount (L : LiteratureInputs) (m : ℕ) :
    {S : BeadSet | S.card = m ∧ beadSize S = m ∧ IsTCore 3 S}.ncard
      = ∑ d ∈ (3 * m + 1).divisors, legendreSym 3 (d : ℤ) :=
  L.three_core_count m

/-- The Matomäki–Radziwiłł gap theorem: the `γ`-th moment of the consecutive gaps of a sieved
multiplicative set `N` below `X` is `O(X * sieveDensity N X ^ (1 - γ))`. -/
@[zf_tag "thm_mr_gap"]
theorem LiteratureInputs.gapTheorem (L : LiteratureInputs) {N : Set ℕ}
    (hN : IsMultiplicativeSet N) {α : ℝ} (hα : 0 < α) {K : ℝ} (hK : 0 < K)
    (hsieve : ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      α * primeRecipSumIoc w z - K / Real.log w
        ≤ primeRecipSumMemIoc w z N)
    {γ : ℝ} (hγ1 : 1 ≤ γ) (hγ2 : γ < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ∑ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
          (fun i => (Nat.nth (· ∈ N) i : ℝ) ≤ X),
        ((Nat.nth (· ∈ N) (i + 1) - Nat.nth (· ∈ N) i : ℝ)) ^ γ
      ≤ C * X * sieveDensity N X ^ (1 - γ) :=
  L.mr_gap N hN α hα K hK hsieve γ hγ1 hγ2

end ZeroFree
