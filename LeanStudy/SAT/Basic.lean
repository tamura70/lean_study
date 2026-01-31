/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic.NormNum

namespace SAT

/-!
Literal is a pair of a variable (α) and its polarity (Bool).
-/
abbrev Literal (α : Type u) := α × Bool

/-- Positive literal has a true polarity. -/
def Literal.isPositive (x : Literal α) := x.2

/-- Complement of a literal. -/
def Literal.negate : Literal α → Literal α :=
  fun x => (x.1, !x.2)

/-- A clause is a list of literals. -/
abbrev Clause (α : Type u) := List (Literal α)

/-- A CNF formula is a list of clauses. -/
abbrev CNF (α : Type u) := List (Clause α)

/-- An assignment is a map α → Bool. -/
abbrev Assignment (α : Type u) := α → Bool

/-- Returns the value of the clause c under the given assignment a. -/
def Clause.eval (a : Assignment α) (c : Clause α) : Bool :=
  c.any (fun x => (a x.1) = x.2)

/-- The clause c is satisfied by an assignment a. -/
def Clause.Sat (a : Assignment α) (c : Clause α) : Prop :=
  Clause.eval a c = true

/-- The clause c is unsatisfiable. -/
def Clause.Unsat (c : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.eval a c = false

/-- The clause c is a tautology. -/
def Clause.Tautology (c : Clause α) : Prop :=
  ∀ (a : α → Bool), Clause.eval a c = true

/-- Returns the value of the CNF f under the given assignment a. -/
def CNF.eval (a : Assignment α) (f : CNF α) : Bool :=
  f.all (fun c => Clause.eval a c)

/-- CNF f is satisfiable with an assignment a. -/
def CNF.Sat (a : Assignment α) (f : CNF α) : Prop :=
  CNF.eval a f = true

/-- CNF f is unsatisfiable. -/
def CNF.Unsat (f : CNF α) : Prop :=
  ∀ a : Assignment α, CNF.eval a f = false

/-- Equivalence of clauses. -/
def Clause.equiv (c1 c2 : Clause α) : Prop :=
  ∀ (a : α → Bool), Clause.eval a c1 = Clause.eval a c2

/-- The empty clause is unsatisfiable. -/
theorem Clause.unsat_of_empty (c : Clause α)
  : c = [] → Clause.Unsat c := by
  intro hc
  rw [hc]
  unfold Clause.Unsat
  exact fun a ↦ Bool.eq_false_of_le_false fun a ↦ a

/-- Clause.equiv is commutative. -/
theorem Clause.equiv_comm (c1 c2 : Clause α)
  : Clause.equiv c1 c2 ↔ Clause.equiv c2 c1 := by
  unfold Clause.equiv
  aesop

/-- Clause.equiv is transitive. -/
theorem Clause.equiv_trans (c1 c2 c3 : Clause α)
  : Clause.equiv c1 c2 → Clause.equiv c2 c3 → Clause.equiv c1 c3 := by
  unfold Clause.equiv
  intros
  simp_all only

/-- Clause c1 and c2 are equivalent if they are equal as sets, that is, c1 ⊆ c2 and c2 ⊆ c1. -/
theorem Clause.equiv_of_same_sets (c1 c2 : Clause α)
  : (c1 ⊆ c2) → (c2 ⊆ c1) → Clause.equiv c1 c2 := by
  intro hs12 hs21 a
  unfold Clause.eval
  grind

/-- Clause c is a tautology if c contains both x and x.negate. -/
theorem Clause.tautology_of_complements (c : Clause α) (x : Literal α)
  : (x ∈ c) → (x.negate ∈ c) → Clause.Tautology c := by
  intro hx hnx
  unfold Clause.Tautology
  unfold Clause.eval
  simp_all only [List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right']
  intro a
  use x.1
  have : a x.1 = x.2 ∨ a x.1 = !x.2 := by
    exact Bool.eq_or_eq_not (a x.1) x.2
  aesop

/-- CNF f is Unsat if f contains the empty clause. -/
theorem CNF.unsat_of_empty_clause (f : CNF α) :
  [] ∈ f → Unsat f := by
  intro hf
  unfold Unsat CNF.eval
  aesop

/-- CNF f is satisfiable if all clauses in f contain the same literal x. -/
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
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right']
  use x.1
  rw [ha1]
  simp_all only [Prod.mk.eta]

/-- CNF f is satisfiable if all clauses in f have a positive literal. -/
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
  simp_all only [Prod.exists, exists_eq_right, Bool.true_eq, Bool.decide_eq_true, List.any_eq_true]

/-- Satisfiability preserving mapping. -/
def CNF.sat_preserving (t : CNF α → CNF β) (ta : (α → Bool) → (β → Bool)) :=
  ∀ f, (∀ a, (CNF.Sat a f) → (CNF.Sat (ta a) (t f))) ∧ ((CNF.Unsat f) → (CNF.Unsat (t f)))

theorem CNF.unsat_rev_of_sat_preserving (t : CNF α → CNF β) (ta : (α → Bool) → (β → Bool))
  : (CNF.sat_preserving t ta) → (∀ f : CNF α, CNF.Unsat (t f) → CNF.Unsat f) := by
  unfold CNF.sat_preserving CNF.Unsat CNF.Sat
  grind

variable (bound_α : Nat)
variable (α := Fin bound_α)

#check CNF α


end SAT
