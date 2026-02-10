/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.SAT.Basic
import LeanStudy.SAT.DirectEncoder
import LeanStudy.CSP.Basic
import LeanStudy.Util

namespace DirectEncoder

open CSP
open SAT

def iX : IVar := { name := "x", lb := 1, ub := 3 }
def iY : IVar := { name := "y", lb := 1, ub := 3 }

abbrev α := IVar × Int

abbrev eq (x : IVar) (i : Int) : Literal α :=
  ((x, i), true)

abbrev ne (x : IVar) (i : Int) : Literal α :=
  ((x, i), false)

abbrev literals (x : IVar) : List (Literal α) :=
  x.dom.map fun i => eq x i

abbrev encode_x (x : IVar) : CNF α :=
  DirectEncoder.EXO.encode (literals x)

#eval toString (eq iX 1)
#eval toString (encode_x iX)

abbrev encode_c (c : Constraint) : CNF α :=
  match c with
  | Constraint.ne x y =>
    let ii := Util.IntRange (max x.lb y.lb) (min x.ub y.ub)
    ii.map (fun i => [ne x i, ne y i])

abbrev encode (csp : CSP) : CNF α :=
  csp.variables.flatMap (fun x => encode_x x) ++
  csp.constraints.flatMap (fun c => encode_c c)

abbrev value_to_assignment (value : IVar → Int) : Assignment α :=
  fun (x, i) => value x = i

lemma value_eq_i_iff_eval_true (value : IVar → Int) (x : IVar) (i : Int) :
  value x = i ↔ (eq x i).eval (value_to_assignment value) = true := by
  norm_num

example (value : IVar → Int) (x : IVar) :
  x.lb ≤ value x → value x ≤ x.ub →
  ∃ l ∈ literals x, l.eval (value_to_assignment value) = true := by
  intros
  use eq x (value x)
  constructor
  · unfold literals
    sorry
  · sorry

lemma sat_cnf_of_sat_csp (value : IVar → Int) (x : IVar) :
  IVar.Sat value x → CNF.Sat (value_to_assignment value) (encode_x x) := by
  set a := value_to_assignment value
  unfold IVar.Sat
  intro h
  unfold encode_x
  rw [DirectEncoder.EXO.sat_iff_card_eq_one]
  unfold Card literals
  simp_all only [List.map_map, Int.ofNat_eq_natCast, List.countP_map]
  sorry


end DirectEncoder
