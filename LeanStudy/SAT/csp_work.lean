/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
section

inductive Term (α : Type) where
  | const : Int → Term α
  | var : α → Term α
  | add : Term α → Term α → Term α

inductive Constraint (α : Type) where
  | eq : Term α → Term α → Constraint α
  | ge : Term α → Term α → Constraint α

structure CSP (α : Type) where
  variables : List α
  domains : α → Int × Int
  constraints : List (Constraint α)

open Term
open Constraint

#check const 1
#check var "x"
#check eq (var "x") (const 1)

def csp1 : CSP String := {
   variables := ["x", "y"]
   domains := fun | "x" => (0,9) | "y" => (1,9) | _ => (0,1)
   constraints := [eq (var "x") (const 1)]
}


end
