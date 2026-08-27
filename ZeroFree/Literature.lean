/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

/-!
# The admitted literature inputs

The formalization boundary of this library is the bibliography of "Zero-free columns in the
character tables of symmetric groups": everything the paper proves is proved here, and everything
it cites to prior literature is admitted. The admitted statements are the fields of
`ZeroFree.LiteratureInputs`.

They are bundled as a structure of hypotheses rather than declared as `axiom`s. An `axiom` is
assumed globally and silently; an explicit argument puts the dependence in the *type* of every
theorem that rests on it, so the main results read, visibly, "assuming Matomäki–Radziwiłł and
Granville–Ono, `D n ≤ C * n ^ (3/4)`", and `#print axioms` remains a genuine check.

Since `LiteratureInputs` cannot be shown nonempty — it contains Matomäki–Radziwiłł — no mechanical
check can detect a field stated more strongly than its source. Each field's docstring therefore
carries the citation it is to be read against.

## The admitted statements

* `eisenstein_criterion`: a positive integer is of the form `x² + xy + y²` exactly when every
  prime `p ≡ 2 mod 3` divides it to an even power. Marshall, *The Loeschian numbers as a problem
  in number theory*.

* `mertens_ap`: Mertens' theorem for arithmetic progressions, asymptotic form,
  `∑_{p ≤ X, p ≡ a mod q} 1/p = (1/φ(q)) log log X + O(1)` for `a` coprime to `q`. Williams,
  *Mertens' theorem for arithmetic progressions*.

* `mertens_ap_uniform`: the same theorem in uniform form, `∑_{w < p ≤ z, p ≡ a mod q} 1/p
  = (1/φ(q)) ∑_{w < p ≤ z} 1/p + O(1/log w)` for `2 ≤ w ≤ z`. Williams, as above. The two Mertens
  forms are separate inputs because they are not equivalent and the paper uses both; deriving
  either from the other is analytic work the paper does not do.

* `tcore_positivity`: for every `t ≥ 4`, every nonnegative integer is the size of some `t`-core.
  Granville–Ono, *Defect zero p-blocks for finite simple groups*, and Ono, *On the positivity of
  the number of t-core partitions*. The proof goes through modular forms. This is what excludes
  every part `≥ 4` and so reduces the problem to cycle types `(3^a, 2^b, 1^c)`.

* `three_core_count`: `c₃(m) = ∑_{d ∣ 3m+1} (d/3)`, where `(·/3)` is the quadratic character
  modulo `3` and `c₃(m)` counts the `3`-cores of size `m`. Granville–Ono, as above. What is
  admitted is the counting formula; the multiplicativity argument that turns it into a criterion
  for `c₃(m) > 0` is proved here, as `exists_isTCore_three_iff`.

* `mr_gap`: the Matomäki–Radziwiłł gap theorem, Matomäki–Radziwiłł, *Multiplicative functions in
  short intervals II*, Corollary 1.2(ii), in the restated form the paper uses. The paper's passage
  from the corollary to that form is a restatement rather than a proof, so what is admitted is its
  output.

## Cited by the paper, but proved here

* **The Murnaghan–Nakayama rule.** `ZeroFree.chi` is *defined* by the Murnaghan–Nakayama
  recursion, since Mathlib has no Specht modules and no `Sₙ` character theory. There is therefore
  no rival definition to reconcile with, the definition is total and computable, and the cutoff
  lemma `exists_chi_eq_zero_of_lt_count` — the engine of the paper — becomes provable. All
  faithfulness to "the character table of `Sₙ`" rests on this one definition.

* **Well-definedness of the `t`-core**, that repeated rim-hook removal reaches a `t`-core
  independent of the order of the removals. Elementary in the abacus/beta-number model, so it is
  proved rather than assumed.

* **The sign twist** `χ^{λ'}(μ) = (-1)^{n-k} χ^λ(μ)` for `μ ⊢ n` with exactly `k` parts, which is
  what forces the number of `2`-cycles in a zero-free column to be even. A citation about the
  character of a Specht module is not evidence about `chi`, which this development defines itself,
  so this is proved from the recursion, as `chi_transpose`: transposing carries a `t`-rim-hook to
  a `t`-rim-hook and sends its height `h` to `t - 1 - h`, so each removal's sign flips by
  `(-1)^(t-1)`, and removing parts summing to `n` in `k` steps flips by `(-1)^(n-k)`.

## Conventions in the analytic half

* **No `IsBigO`.** Every `≪` becomes an explicit constant, explicitly quantified:
  `∃ C > 0, ∀ X ≥ 3, lhs ≤ C * rhs`. The paper's implied constants depend on its parameters, and
  an `IsBigO` over a filter buries that dependence exactly where it has to be used.

* **`Nat.nth` for gap sequences.** An increasing enumeration `a₁ < a₂ < ⋯` of a set of naturals,
  with consecutive gaps `a_{i+1} - a_i`, is `Nat.nth (· ∈ A)`; this needs the set infinite, which
  for the sieve set holds because every prime `p ≡ 1 mod 9` lies in it.

* **`s₂` and `s₃` are infima of nonempty sets of shifts.** For `s₃`, take `m ∈ {0,1,2}` congruent
  to `n` mod `3` and note that `3m + 1 ∈ {1,4,7}` is Loeschian; for `s₂`, take `m ∈ {0,1}` of the
  right parity, `0` and `1` both being triangular. Hence `s₃ n ≤ n/3` and `s₂ n ≤ n/2`.
-/
