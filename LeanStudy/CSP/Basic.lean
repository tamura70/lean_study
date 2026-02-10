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
deriving Repr

instance : ToString IVar where
  toString x := x.name

abbrev IVar.dom (x : IVar) : List Int :=
  Util.IntRange x.lb x.ub

abbrev IVar.Sat (value : IVar → Int) (x : IVar) : Prop :=
  x.lb ≤ value x ∧ value x ≤ x.ub

/-! Constraint -/
inductive Constraint where
| ne (x : IVar) (y : IVar) : Constraint

abbrev Constraint.Sat (value : IVar → Int) (c : Constraint) : Prop :=
  match c with
  | Constraint.ne x y => value x ≠ value y

end CSP

open CSP

/-! CSP -/
structure CSP where
  ivariables : List IVar
  constraints : List Constraint

abbrev CSP.Sat (value : IVar → Int) (csp : CSP) : Prop :=
  (∀ x ∈ csp.ivariables, IVar.Sat value x) ∧
  (∀ c ∈ csp.constraints, Constraint.Sat value c)

end
