/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean

/-!
# The `zf_tag` attribute

`@[zf_tag "TAG"]` labels a Lean declaration with the name of the mathematical statement it
formalizes, in the style of Mathlib's `@[stacks TAG]`. The attribute takes a single string, such as
`def_chi`, `lem_cutoff`, `prop_duro` or `thm_pointwise`.

## Main definitions

* `zfTag`: the attribute syntax `zf_tag "TAG"`.
* `zfTagAttr`: the parametric attribute recording each labelled declaration's tag.
-/

public meta section

open Lean

/-- `@[zf_tag "TAG"]` labels a Lean declaration with the tag of the statement it formalizes.

The syntax node is named `zfTag` rather than `zf_tag`: the user-facing token keeps the underscore,
but Mathlib's `defsWithUnderscore` linter inspects the declaration name, which must therefore be
lowerCamelCase. -/
syntax (name := zfTag) "zf_tag " str : attr

/-- Records, for each labelled declaration, the tag of the statement it formalizes. -/
initialize zfTagAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `zfTag
    descr := "Links a Lean declaration to the name of the result it formalizes."
    getParam := fun _ stx => do
      match stx with
      | `(attr| zf_tag $s:str) => return s.getString
      | _ => throwError "zf_tag takes exactly one string literal, the name of the result"
  }
