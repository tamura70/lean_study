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
    (Util.IntRange (max x.lb y.lb) (min x.ub y.ub)).map (fun i => [x_ne x i, x_ne y i])

abbrev encode (csp : CSP) : CNF α :=
  csp.ivariables.flatMap (fun x => encode_x x) ++
  csp.constraints.flatMap (fun c => encode_c c)

abbrev val_to_a (val : Valuation) : Assignment α :=
  fun (x, i) => val x = i

lemma x_eq_injective (x : IVar) :
  Function.Injective (x_eq x) := by
  unfold Function.Injective
  norm_num

lemma count_literals_eq_one_iff_bound (x : IVar) (i : Int) :
  List.count (x_eq x i) (literals x) = 1 ↔ x.lb ≤ i ∧ i ≤ x.ub := by
  unfold literals
  let r := Util.IntRange x.lb x.ub
  rw [Util.count_injective i r (x_eq x) (x_eq_injective x)]
  exact Util.count_intrange_eq_one_iff_bound x.lb x.ub i

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

theorem sat_ivar_iff_sat_cnf (val : Valuation) (x : IVar) :
  CNF.Sat (val_to_a val) (encode_x x) ↔ IVar.Sat val x := by
  unfold IVar.Sat
  rw [sat_encode_x_iff_countP_eq_one]
  let p := fun x => Literal.eval (val_to_a val) x
  let q := fun x1 => x1 == x_eq x (val x)
  have : ∀ x1 ∈ (literals x), (p x1 = true) ↔ (q x1 = true) := by
    grind
  rw [List.countP_congr this]
  have := count_literals_eq_one_iff_bound x (val x)
  unfold List.count at this
  rw [this]

lemma val_ne_iff_all_ne (val : Valuation) (x y : IVar) (hx : IVar.Sat val x) (hy : IVar.Sat val y) :
  ¬ (val x = val y) ↔ ∀ i, max x.lb y.lb ≤ i → i ≤ min x.ub y.ub → val x ≠ i ∨ val y ≠ i := by
  grind

lemma sat_clause_x_ne_iff_ne_or_ne (val : Valuation) (x y : IVar) (i : Int) :
  Clause.Sat (val_to_a val) [x_ne x i, x_ne y i] ↔ val x ≠ i ∨ val y ≠ i := by
  unfold Clause.Sat val_to_a Literal.eval
  norm_num

lemma sat_cnf_x_ne_iff_all_ne_or_ne (val : Valuation) (x y : IVar) :
  CNF.Sat (val_to_a val) (encode_c (Constraint.ne x y)) ↔
  ∀ i, max x.lb y.lb ≤ i → i ≤ min x.ub y.ub → val x ≠ i ∨ val y ≠ i := by
  unfold CNF.Sat
  constructor
  · intro h i hi1 hi2
    rw [← sat_clause_x_ne_iff_ne_or_ne val x y i]
    unfold encode_c at h
    have := h [x_ne x i, x_ne y i]
    sorry
  · intro h

    sorry

  rw [sat_clause_x_ne_iff_ne_or_ne val x y]

   encode_c val_to_a
  unfold Clause.Sat Literal.eval

  simp only [List.mem_map, List.mem_ite_nil_left, lt_sup_iff, inf_lt_iff, not_or, not_lt,
    List.map_map, List.mem_range, Function.comp_apply, ↓existsAndEq, and_true, decide_eq_true_eq,
    Prod.exists, Bool.exists_bool, decide_eq_false_iff_not, forall_exists_index, and_imp,
    sup_le_iff, le_inf_iff, ne_eq]
  try?
  norm_num
  sorry

lemma sat_ne_iff_sat_cnf (val : Valuation) (c : Constraint) (hc : c = Constraint.ne x y)
  (hx : IVar.Sat val x) (hy : IVar.Sat val y) :
  Constraint.Sat val c ↔ CNF.Sat (val_to_a val) (encode_c c) := by
  unfold Constraint.Sat
  simp only [ne_eq]
  rw [val_ne_iff_all_ne]
  unfold encode_c
  simp only [sup_le_iff, le_inf_iff, ne_eq, and_imp]
  sorry -- TODO

theorem sat_constraint_iff_sat_cnf (val : Valuation) (c : Constraint) :
  CNF.Sat (val_to_a val) (encode_c c) ↔ Constraint.Sat val c := by
  match c with
  | Constraint.ne x y =>
    exact Iff.symm (sat_ne_iff_sat_cnf val (Constraint.ne x y) rfl)

end DirectEncoder
