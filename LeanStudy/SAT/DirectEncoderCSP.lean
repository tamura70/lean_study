/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.SAT.Basic
import LeanStudy.SAT.DirectEncoder
import LeanStudy.CSP.Basic
import LeanStudy.Util
import Mathlib.Tactic.NormNum

namespace DirectEncoder

open CSP
open SAT

def iX : IVar := { name := "x", lb := 1, ub := 3 }
def iY : IVar := { name := "y", lb := 1, ub := 3 }

abbrev α := IVar × Nat

abbrev x_eq (x : IVar) (i : Nat) : Literal α :=
  ((x, i), true)

abbrev x_ne (x : IVar) (i : Nat) : Literal α :=
  ((x, i), false)

abbrev literals (x : IVar) : List (Literal α) :=
  (Util.Range x.lb x.ub).map (x_eq x)

abbrev encode_x (x : IVar) : CNF α :=
  DirectEncoder.EXO.encode (literals x)

#eval toString (x_eq iX 1)
#eval toString (encode_x iX)

abbrev encode_c (c : Constraint) : CNF α :=
  match c with
  | Constraint.ne x y =>
    let ii := Util.Range (max x.lb y.lb) (min x.ub y.ub)
    ii.map (fun i => [x_ne x i, x_ne y i])

abbrev encode (csp : CSP) : CNF α :=
  csp.ivariables.flatMap (fun x => encode_x x) ++
  csp.constraints.flatMap (fun c => encode_c c)

abbrev value_to_assignment (value : IVar → Nat) : Assignment α :=
  fun (x, i) => value x = i

lemma x_eq_true_iff_value_eq_i (value : IVar → Nat) (x : IVar) (i : Nat) :
  (x_eq x i).eval (value_to_assignment value) = true ↔ value x = i := by
  norm_num

lemma x_eq_true (value : IVar → Nat) (x : IVar) :
  (x_eq x (value x)).eval (value_to_assignment value) = true := by
  norm_num

lemma x_ne_fale_iff_value_eq_i (value : IVar → Nat) (x : IVar) (i : Nat) :
  (x_ne x i).eval (value_to_assignment value) = false ↔ value x = i := by
  norm_num

lemma x_ne_false (value : IVar → Nat) (x : IVar) :
  (x_ne x (value x)).eval (value_to_assignment value) = false := by
  norm_num

lemma x_eq_injective (x : IVar) :
  Function.Injective (x_eq x) := by
  unfold Function.Injective
  norm_num

lemma count_literals_eq_one (x : IVar) (i : Nat) (h1 : x.lb ≤ i) (h2 : i ≤ x.ub) :
  List.count (x_eq x i) (literals x) = 1 := by
  unfold literals
  let r := Util.Range x.lb x.ub
  rw [Util.count_injective i r (x_eq x) (x_eq_injective x)]
  sorry

lemma sat_encode_x_iff_countP_eq_one (x : IVar) :
  ∀ a, CNF.Sat a (encode_x x) ↔ List.countP (fun x1 => x1.eval a) (literals x) = 1 := by
  intro a
  unfold encode_x
  constructor
  · rw [DirectEncoder.EXO.sat_iff_card_eq_one]
    unfold Card
    gcongr
  · rw [DirectEncoder.EXO.sat_iff_card_eq_one]
    unfold Card
    gcongr

lemma sat_cnf_of_sat_ivar (value : IVar → Nat) (x : IVar) :
  IVar.Sat value x → CNF.Sat (value_to_assignment value) (encode_x x) := by
  unfold IVar.Sat
  intro h
  obtain ⟨ h1, h2 ⟩ := h
  rw [sat_encode_x_iff_countP_eq_one]
  let p := fun x => Literal.eval (value_to_assignment value) x
  let q := fun x1 => x1 == x_eq x (value x)
  have : ∀ x1 ∈ (literals x), (p x1 = true) ↔ (q x1 = true) := by
    grind
  rw [List.countP_congr this]
  exact count_literals_eq_one x (value x) h1 h2

lemma sat_ivar_of_sat_cnf (value : IVar → Nat) (x : IVar) :
  CNF.Sat (value_to_assignment value) (encode_x x) → IVar.Sat value x := by
  unfold IVar.Sat
  rw [sat_encode_x_iff_countP_eq_one]
  let p := fun x => Literal.eval (value_to_assignment value) x
  let q := fun x1 => x1 == x_eq x (value x)
  have : ∀ x1 ∈ (literals x), (p x1 = true) ↔ (q x1 = true) := by grind
  rw [List.countP_congr this]
  intro h
  unfold literals at h
  set r := Util.Range x.lb x.ub
  by_contra
  have : value x ∉ r := by
    simp only [not_and_or] at this
    obtain hx1 | hx2 := this
    case _ =>
      grind
    case _ =>
      sorry
  have : value x ∈ r := by
    rw [Util.countP_map r (x_eq x) q] at h
    have : List.count (value x) r = 1:= by
      grind only [List.countP_eq_zero, List.count_eq_zero]
    grind only [List.count_eq_zero]
  contradiction

theorem sat_ivar_iff_sat_cnf (value : IVar → Nat) (x : IVar) :
  CNF.Sat (value_to_assignment value) (encode_x x) ↔ IVar.Sat value x := by
  constructor
  · exact fun a ↦ sat_ivar_of_sat_cnf value x a
  · exact fun a ↦ sat_cnf_of_sat_ivar value x a

lemma sat_ne_iff_sat_cnf (value : IVar → Nat) (c : Constraint) (hc : c = Constraint.ne x y) :
  Constraint.Sat value c ↔ CNF.Sat (value_to_assignment value) (encode_c c) := by
  unfold CNF.Sat
  simp?
  set x1 := c.1; set x2 := c.2
  constructor
  · intro h v hv
    sorry
  · intro h
    have h := h (value x1 - max x1.lb x2.lb)
    norm_num at h
    have : value x1 - max x1.lb x2.lb < min x1.ub x2.ub - max x1.lb x2.lb + 1 := by
      sorry
    sorry

theorem sat_constraint_iff_sat_cnf (value : IVar → Nat) (c : Constraint) :
  CNF.Sat (value_to_assignment value) (encode_c c) ↔ Constraint.Sat value c := by
  match c with
  | Constraint.ne x y =>
    exact Iff.symm (sat_ne_iff_sat_cnf value (Constraint.ne x y) rfl)

end DirectEncoder
