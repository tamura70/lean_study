/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib

/-!
Under Constructio

SAT solver および SAT encoding に関する定理を示す。
-/
section

open Std.Sat
open Std.Sat.Literal
open Std.Sat.CNF
open Std.Sat.CNF.Clause

/-!
Literal
-/

/--
Literal x について x.negate.negate は x に等しい
-/
theorem Literal.complement_complement (x : Literal α)
  : x.negate.negate = x := by
  unfold Std.Sat.Literal.negate
  norm_num

/-!
Clause
-/

/--
Clause c の unsat の定義: すべての付値 a :　α → Bool に対して Clause.eval a c の値が false
-/
def Clause.unsat (c : Clause α) :=
  ∀ (a : α → Bool), Clause.eval a c = false

/--
Clause c の sat の定義: ある付値 a :　α → Bool に対して Clause.eval a c の値が true
-/
def Clause.sat (c : Clause α) :=
  ∃ (a : α → Bool), Clause.eval a c = true

/--
Clause c の tautology の定義: すべての付値 a : α → Bool に対して Clause.eval a c の値が true
-/
def Clause.tautology (c : Clause α) :=
  ∀ (a : α → Bool), Clause.eval a c = true

/--
Clause c1, c2 の equiv の定義: すべての付値 a :　α → Bool に対して Clause.eval の値が等しい
-/
def Clause.equiv (c1 c2 : Clause α) :=
  ∀ (a : α → Bool), Clause.eval a c1 = Clause.eval a c2

/--
Clause c が空なら c は unsat
-/
theorem Clause.unsat_of_empty (c : Clause α)
  : c = [] → Clause.unsat c := by
  intro hc
  rw [hc]
  unfold Clause.unsat
  norm_num

/--
Clause c が Literal x と x.negate を含むなら c は tautology
-/
theorem Clause.tautology_of_complements (c : Clause α) (x : Literal α)
  : x ∈ c → x.negate ∈ c → Clause.tautology c := by
  intro hx hnx
  let v := x.1
  let sign1 := x.2
  let sign2 := x.negate.2
  unfold Clause.tautology
  unfold Clause.eval
  by_contra h
  simp_all only
    [List.any_eq_true, beq_iff_eq, Prod.exists, exists_eq_right', not_forall, not_exists]
  rcases h with ⟨ a, h1 ⟩
  have h2 : (v, a v) ∉ c := h1 v
  obtain (hav1 | hav2) : (a v = sign1 ∨ a v = sign2) := by
    have hs : sign2 = ! sign1 := by bound
    rw [hs]
    exact Bool.eq_or_eq_not (a v) sign1
  case _ =>
    rw [hav1] at h2
    bound
  case _ =>
    rw [hav2] at h2
    bound

/--
Clause.equiv の交換律
-/
theorem Clause.equiv_comm (c1 c2 : Clause α)
  : Clause.equiv c1 c2 ↔ Clause.equiv c2 c1 := by
  unfold Clause.equiv
  aesop

/--
Clause.equiv の推移律
-/
theorem Clause.equiv_trans (c1 c2 c3 : Clause α)
  : Clause.equiv c1 c2 → Clause.equiv c2 c3 → Clause.equiv c1 c3 := by
  unfold Clause.equiv
  intros
  simp_all only

/--
Clause c1, c2 について c1 ⊆ c2 で c2 ⊆ c1 なら c1 と c2 は equiv
-/
theorem Clause.equiv_of_same_sets (c1 c2 : Clause α)
  : List.Subset c1 c2 → List.Subset c2 c1 → Clause.equiv c1 c2 := by
  unfold List.Subset Clause.equiv
  intro hs12 hs21 a
  obtain (h1t | h1f) : (Clause.eval a c1 = true ∨ Clause.eval a c1 = false) := by
    norm_num
  case _ =>
    rw [h1t]
    symm
    show Clause.eval a c2 = true
    unfold Clause.eval at *
    simp_all only [List.any_eq_true, beq_iff_eq, Prod.exists, exists_eq_right']
    -- h1t : ∃ v, (v, a v) ∈ c1
    rcases h1t with ⟨ v, hv ⟩
    use v
    exact Multiset.mem_coe.mp (hs12 (hs21 (hs12 hv)))
  case _ =>
    rw [h1f]
    symm
    show Clause.eval a c2 = false
    unfold Clause.eval at *
    simp_all only [List.any_eq_false, beq_iff_eq, Prod.forall, Bool.forall_bool, Bool.not_eq_false,
      Bool.not_eq_true]
    intro v
    apply And.intro
    · change (v, false) ∈ c2 → True
      intro h
      simp_all only
    · change (v, true) ∈ c2 → True
      intro h
      simp_all only

/-!
CNF
-/

/--
CNF f について f が空節を含むなら　f は Unsat
-/
theorem CNF.unsat_of_empty_clause (f : CNF α) :
  [] ∈ f → Unsat f := by
  intro hf
  unfold Unsat CNF.eval
  aesop

/--
CNF f と Literal x について f のすべての Clause が x を含むなら　f は Sat
-/
theorem CNF.sat_of_same_literal (f : CNF α) (x : Literal α)
  : (∀ c, c ∈ f → x ∈ c) → (∃ a, CNF.Sat a f) := by
  intro hc
  have : ∃ (a : α → Bool), a x.1 = x.2 := by
    exact exists_apply_eq x.1 x.2
  rcases this with ⟨ a1, ha1 ⟩
  use a1
  show Sat a1 f
  unfold Sat CNF.eval
  simp only [List.all_eq_true]
  intro c hc1
  show Clause.eval a1 c = true
  unfold Clause.eval
  simp only [List.any_eq_true, beq_iff_eq, Prod.exists, exists_eq_right']
  use x.1
  rw [ha1]
  simp_all only

/--
CNF f について f のすべての Clause が正リテラルを含むなら f は Sat
-/
theorem CNF.sat_of_positive_literal (f : CNF α)
  : (∀ c, c ∈ f → (∃ x ∈ c, x.2 = true)) → (∃ a, CNF.Sat a f) := by
  intro hc
  have : ∃ (a : α → Bool), ∀ v, a v = true := by
    exact Exists.intro (fun a ↦ true) (congrFun rfl)
  rcases this with ⟨ a1, ha1 ⟩
  use a1
  show Sat a1 f
  unfold Sat CNF.eval
  simp only [List.all_eq_true]
  intro c hc1
  show Clause.eval a1 c = true
  unfold Clause.eval
  simp_all only [Prod.exists, exists_eq_right, Bool.true_beq, List.any_eq_true]

end
