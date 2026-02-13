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

abbrev all_val_ne (val : Valuation) (x y : IVar) :=
  ∀ i, max x.lb y.lb ≤ i ∧ i ≤ min x.ub y.ub → val x ≠ i ∨ val y ≠ i

lemma val_ne_iff_all_ne (val : Valuation) (x y : IVar) (hx : IVar.Sat val x) (hy : IVar.Sat val y) :
  ¬ (val x = val y) ↔ all_val_ne val x y := by
  grind

lemma sat_ne_of_all_val_ne (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) (hx : IVar.Sat val x) (hy : IVar.Sat val y) :
  all_val_ne val x y → Constraint.Sat val c := by
  unfold Constraint.Sat
  simp only [ne_eq]
  have : c.1 = x := by simp_all only
  rw [this]
  have : c.2 = y := by simp_all only
  rw [this]
  grind

lemma all_val_ne_of_sat_ne (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) :
  Constraint.Sat val c → all_val_ne val x y := by
  unfold Constraint.Sat
  simp only [ne_eq]
  have : c.1 = x := by simp_all only
  rw [this]
  have : c.2 = y := by simp_all only
  rw [this]
  omega

lemma sat_cnf_of_all_val_ne (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) :
  all_val_ne val x y → CNF.Sat (val_to_a val) (encode_c c) := by
  intro h
  unfold CNF.Sat encode_c
  set lb := max x.lb y.lb
  set ub := min x.ub y.ub
  intro cx hcx
  set p1 := fun i => [x_ne x i, x_ne y i] = cx
  have : ∃ i, lb ≤ i ∧ i ≤ ub ∧ p1 i := by
    have := (Util.exists_intrange_iff_exists_bound' lb ub p1).mp
    apply this
    aesop
  obtain ⟨ i, hi ⟩ := this
  unfold Clause.Sat val_to_a
  have : val x ≠ i ∨ val y ≠ i := by grind only
  obtain hx | hy := this
  case _ =>
    use x_ne x i
    grind
  case _ =>
    use x_ne y i
    grind

lemma all_val_ne_of_sat_cnf (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) :
  CNF.Sat (val_to_a val) (encode_c c) → all_val_ne val x y := by
  unfold CNF.Sat val_to_a encode_c all_val_ne
  intro h
  simp only [List.mem_map] at h
  have : c.1 = x := by simp_all only
  rw [this] at h
  have : c.2 = y := by simp_all only
  rw [this] at h
  set lb := max x.lb y.lb
  set ub := min x.ub y.ub
  intro i hi
  have h := h [x_ne x i, x_ne y i]
  set p := fun i1 => [x_ne x i1, x_ne y i1] = [x_ne x i, x_ne y i]
  have := Util.exists_intrange_iff_exists_bound' lb ub p
  rw [this] at h
  unfold Clause.Sat at h
  aesop

lemma sat_ne_of_sat_cnf (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) (hx : IVar.Sat val x) (hy : IVar.Sat val y) :
  CNF.Sat (val_to_a val) (encode_c c) → Constraint.Sat val c := by
  intro h
  apply sat_ne_of_all_val_ne val c hc hx hy
  apply all_val_ne_of_sat_cnf val c hc at h
  assumption

lemma sat_cnf_of_sat_ne (val : Valuation) (c : Constraint)
  (hc : c = Constraint.ne x y) :
  Constraint.Sat val c → CNF.Sat (val_to_a val) (encode_c c) := by
  intro h
  apply sat_cnf_of_all_val_ne val c hc
  apply all_val_ne_of_sat_ne val c hc at h
  assumption

lemma sat_constraint_of_sat_cnf (val : Valuation) (c : Constraint)
  (h : ∀ x ∈ c.ivars, IVar.Sat val x) :
  CNF.Sat (val_to_a val) (encode_c c) → Constraint.Sat val c := by
  match c with
  | Constraint.ne x y =>
    let c1 := Constraint.ne x y
    have hx : IVar.Sat val x := by grind
    have hy : IVar.Sat val y := by grind
    apply sat_ne_of_sat_cnf val c1 rfl hx hy

lemma sat_cnf_of_sat_constraint (val : Valuation) (c : Constraint) :
  Constraint.Sat val c → CNF.Sat (val_to_a val) (encode_c c) := by
  match c with
  | Constraint.ne x y =>
    let c1 := Constraint.ne x y
    apply sat_cnf_of_sat_ne val c1 rfl

lemma sat_csp_of_sat_cnf (val : Valuation) (csp : CSP) :
  CNF.Sat (val_to_a val) (encode csp) → CSP.Sat val csp := by
  unfold encode
  rw [CNF.sat_append_iff_sat_and]
  repeat rw [CNF.sat_flatmap_iff_sat_all]
  intro ⟨ h1, h2 ⟩
  have h1 : ∀ x ∈ csp.ivariables, IVar.Sat val x := by
    exact fun x a ↦ (fun val x ↦ (sat_ivar_iff_sat_cnf val x).mp) val x (h1 x a)
  unfold CSP.Sat
  constructor
  · assumption
  · intro c hc
    have h := h2 c hc
    have : ∀ x ∈ c.ivars, IVar.Sat val x := by
      intro x hx
      have : x ∈ csp.ivariables := csp.wf c hc x hx
      (expose_names; exact (sat_ivar_iff_sat_cnf val x).mp (h1_1 x this))
    exact sat_constraint_of_sat_cnf val c this (h2 c hc)

lemma sat_cnf_of_sat_csp (val : Valuation) (csp : CSP) :
  CSP.Sat val csp → CNF.Sat (val_to_a val) (encode csp) := by
  unfold CSP.Sat
  intro ⟨ h1, h2 ⟩
  unfold encode
  rw [CNF.sat_append_iff_sat_and]
  repeat rw [CNF.sat_flatmap_iff_sat_all]
  constructor
  · intro x hx
    have h1 := h1 x hx
    (expose_names; exact (sat_ivar_iff_sat_cnf val x).mpr (h1_1 x hx))
  · intro c hc
    have h2 := h2 c hc
    (expose_names; exact sat_cnf_of_sat_constraint val c (h2_1 c hc))

theorem sat_csp_iff_sat_cnf (val : Valuation) (csp : CSP) :
  CNF.Sat (val_to_a val) (encode csp) ↔ CSP.Sat val csp := by
  constructor
  · exact fun a ↦ sat_csp_of_sat_cnf val csp a
  · exact fun a ↦ sat_cnf_of_sat_csp val csp a

end DirectEncoder
