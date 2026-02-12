/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.Util

section

namespace CSP

/-! IVar -/
structure IVar where
  name : String
  lb : Int
  ub : Int
deriving Repr, DecidableEq

instance : ToString IVar where
  toString x := x.name

abbrev Valuation := IVar → Int

abbrev IVar.size (x : IVar) : Int :=
  x.ub - x.lb + 1

abbrev IVar.Sat (valuation : Valuation) (x : IVar) : Prop :=
  x.lb ≤ valuation x ∧ valuation x ≤ x.ub

/-! Constraint -/
inductive Constraint where
| ne (x : IVar) (y : IVar) : Constraint

abbrev Constraint.Sat (valuation : Valuation) (c : Constraint) : Prop :=
  match c with
  | Constraint.ne x y => valuation x ≠ valuation y

end CSP

open CSP

/-! CSP -/
structure CSP where
  ivariables : List IVar
  constraints : List Constraint

abbrev CSP.Sat (valuation : Valuation) (csp : CSP) : Prop :=
  (∀ x ∈ csp.ivariables, IVar.Sat valuation x) ∧
  (∀ c ∈ csp.constraints, Constraint.Sat valuation c)

end
