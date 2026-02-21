/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.List.Nodup
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import LeanStudy.SAT.Basic
-- import Mathlib.Tactic.NormNum

section

namespace SAT

-- variable (α : Type) [DecidableEq α] [Hashable α]
abbrev α := String

/-- List of varibles in the clause. -/
abbrev Clause.variables (c : Clause α) : Std.HashSet α :=
  Std.HashSet.ofList (c.map (fun x => x.1))

/-- List of varibles in the CNF formula. -/
abbrev CNF.variables (f : CNF α) : Std.HashSet α :=
  (f.map (fun c => c.variables)).foldl Std.HashSet.union {}

abbrev CNF.subst (x : Literal α) (f : CNF α) : CNF α :=
  (f.filter (fun c => ! c.contains x)).map
  (fun c => c.filter (fun x1 => x1 != x.negate))

abbrev CNF.substOpt (x : Literal α) (f : CNF α) : Option (CNF α) :=
  let f1 := CNF.subst x f
  if [] ∈ f1 then none else some f1

#check CNF.subst

def solver1 (f : CNF α) : Option (Std.HashMap α Bool) :=
  let rec search (vs : List α) (f: CNF α) : Option (Std.HashMap α Bool) :=
    let rec decide (v : α) (sign : Bool) (vs : List α) (f : CNF α) : Option (Std.HashMap α Bool) :=
      f.substOpt (v, sign) >>= fun g =>
      search vs g >>= fun a =>
      some (a.insert v sign)
    match vs with
    | [] =>
      some {}
    | v :: vs =>
      (decide v false vs f) <|> (decide v true vs f)
  search f.variables.toList f

end SAT
end

section

open SAT

def p : Literal α := ("p", true)
def q : Literal α := ("q", true)

def cnf1 : CNF α := [
  [p, q],
  [p.negate, q.negate]
]

#check cnf1
#eval cnf1.variables
#eval CNF.substOpt p cnf1
#eval solver1 cnf1





end
