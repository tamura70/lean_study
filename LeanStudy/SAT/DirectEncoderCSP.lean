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

abbrev α := IVar × Int

abbrev x_eq (x : IVar) (i : Int) : Literal α :=
  ((x, i), true)

abbrev x_ne (x : IVar) (i : Int) : Literal α :=
  ((x, i), false)

abbrev literals (x : IVar) : List (Literal α) :=
  (Util.IntRange x.lb x.ub).map (x_eq x)

abbrev encode_x (x : IVar) : CNF α :=
  DirectEncoder.EXO.encode (literals x)

#eval toString (x_eq iX 1)
#eval toString (encode_x iX)

abbrev encode_c (c : Constraint) : CNF α :=
  match c with
  | Constraint.ne x y =>
    let ii := Util.IntRange (max x.lb y.lb) (min x.ub y.ub)
    ii.map (fun i => [x_ne x i, x_ne y i])

abbrev encode (csp : CSP) : CNF α :=
  csp.ivariables.flatMap (fun x => encode_x x) ++
  csp.constraints.flatMap (fun c => encode_c c)

abbrev val_to_a (val : Valuation) : Assignment α :=
  fun (x, i) => val x = i

lemma x_eq_true_iff_val_eq (val : Valuation) (x : IVar) (i : Int) :
  (x_eq x i).eval (val_to_a val) = true ↔ val x = i := by
  norm_num

lemma x_eq_true (val : Valuation) (x : IVar) :
  (x_eq x (val x)).eval (val_to_a val) = true := by
  norm_num

lemma x_ne_fale_iff_val_eq_i (val : Valuation) (x : IVar) (i : Int) :
  (x_ne x i).eval (val_to_a val) = false ↔ val x = i := by
  norm_num

lemma x_ne_false (val : Valuation) (x : IVar) :
  (x_ne x (val x)).eval (val_to_a val) = false := by
  norm_num

lemma x_eq_injective (x : IVar) :
  Function.Injective (x_eq x) := by
  unfold Function.Injective
  norm_num

lemma count_literals_eq_one (x : IVar) (i : Int) (h : x.lb ≤ i ∧ i ≤ x.ub) :
  List.count (x_eq x i) (literals x) = 1 := by
  unfold literals
  let r := Util.IntRange x.lb x.ub
  rw [Util.count_injective i r (x_eq x) (x_eq_injective x)]
  exact Util.count_intrange_eq_one x.lb x.ub i h

lemma sat_encode_x_iff_countP_eq_one (x : IVar) :
  ∀ a, CNF.Sat a (encode_x x) ↔ List.countP (fun lit => lit.eval a) (literals x) = 1 := by
  intro a
  unfold encode_x
  constructor
  · rw [DirectEncoder.EXO.sat_iff_card_eq_one]
    unfold Card
    gcongr
  · rw [DirectEncoder.EXO.sat_iff_card_eq_one]
    unfold Card
    gcongr

lemma sat_cnf_of_sat_ivar (val : Valuation) (x : IVar) :
  IVar.Sat val x → CNF.Sat (val_to_a val) (encode_x x) := by
  unfold IVar.Sat
  intro h
  rw [sat_encode_x_iff_countP_eq_one]
  let p := fun x => Literal.eval (val_to_a val) x
  let q := fun x1 => x1 == x_eq x (val x)
  have : ∀ x1 ∈ (literals x), (p x1 = true) ↔ (q x1 = true) := by
    grind
  rw [List.countP_congr this]
  exact count_literals_eq_one x (val x) h

lemma sat_ivar_of_sat_cnf (val : Valuation) (x : IVar) :
  CNF.Sat (val_to_a val) (encode_x x) → IVar.Sat val x := by
  unfold IVar.Sat
  rw [sat_encode_x_iff_countP_eq_one]
  let p := fun x => Literal.eval (val_to_a val) x
  let q := fun x1 => x1 == x_eq x (val x)
  have : ∀ x1 ∈ (literals x), (p x1 = true) ↔ (q x1 = true) := by grind
  rw [List.countP_congr this]
  intro h
  unfold literals at h
  set r := Util.IntRange x.lb x.ub
  sorry -- TODO
  /-
  by_contra
  have : val x ∉ r := by
    simp only [not_and_or] at this
    obtain hx1 | hx2 := this
    case _ =>
      grind
    case _ =>
      sorry
  have : val x ∈ r := by
    rw [Util.countP_map r (x_eq x) q] at h
    have : List.count (val x) r = 1:= by
      grind only [List.countP_eq_zero, List.count_eq_zero]
    grind only [List.count_eq_zero]
  contradiction
  -/

theorem sat_ivar_iff_sat_cnf (val : Valuation) (x : IVar) :
  CNF.Sat (val_to_a val) (encode_x x) ↔ IVar.Sat val x := by
  constructor
  · exact fun a ↦ sat_ivar_of_sat_cnf val x a
  · exact fun a ↦ sat_cnf_of_sat_ivar val x a

lemma sat_ne_iff_sat_cnf (val : Valuation) (c : Constraint) (hc : c = Constraint.ne x y) :
  Constraint.Sat val c ↔ CNF.Sat (val_to_a val) (encode_c c) := by
  sorry -- TODO

theorem sat_constraint_iff_sat_cnf (val : Valuation) (c : Constraint) :
  CNF.Sat (val_to_a val) (encode_c c) ↔ Constraint.Sat val c := by
  match c with
  | Constraint.ne x y =>
    exact Iff.symm (sat_ne_iff_sat_cnf val (Constraint.ne x y) rfl)

end DirectEncoder
