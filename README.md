[![](logo.svg)](https://axiommath.ai/)

# Zero-Free Columns in Character Tables of Symmetric Groups

This is a Lean formalization of two upper bounds on the number of zero-free columns in the character table of a symmetric group.

## Main Results

Write `D(n)` for the number of conjugacy classes of `S_n` on which no irreducible character vanishes. Both results assume six cited statements from the literature, bundled as `ZeroFree.LiteratureInputs`.

* `D(n)` is at most a constant times `n^{3/4}`, for every `n ≥ 1`.
* For every `B > 5/6` there is a `C_B > 0` such that `D(n) > C_B n^{1/2} (log n)^B` holds for at most `C X (log X)^{-(1/2)(B - 5/6) + ε}` of the integers `n ≤ X`, for every `ε > 0` and every `X ≥ 3`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Comparator/Challenge.lean](Comparator/Challenge.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
