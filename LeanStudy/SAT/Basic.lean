/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic.NormNum

section

namespace SAT

/-!
Definitions of assignments.
-/

/-- An assignment is a map α → Bool. -/
abbrev Assignment (α : Type u) := α → Bool

/-!
Definitions of literals.
-/

/-- A literal is a pair of α and Bool. -/
abbrev Literal (α : Type u) := α × Bool

/-- Positive literal has a true polarity. -/
abbrev Literal.isPositive (x : Literal α) := x.2

/-- Complement of a literal. -/
abbrev Literal.negate : Literal α → Literal α :=
  fun x => (x.1, !x.2)

/-- Returns the value of the literal x under the given assignment a. -/
abbrev Literal.eval (a : Assignment α) (x : Literal α) : Bool :=
  (a x.1) = x.2

/-!
Definitions of clauses.
-/

/-- A clause is a list of literals. -/
abbrev Clause (α : Type u) := List (Literal α)

/-- The clause c is satisfied by an assignment a. -/
abbrev Clause.Sat (a : Assignment α) (c : Clause α) : Prop :=
  ∃ x ∈ c, x.eval a = true

/-- The clause c is unsatisfiable. -/
abbrev Clause.Unsat (c : Clause α) : Prop :=
  ∀ a : Assignment α, ¬ Clause.Sat a c

/-- The clause c is a tautology. -/
abbrev Clause.Tautology (c : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.Sat a c

/-- Equivalence of clauses. -/
abbrev Clause.equiv (c1 c2 : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.Sat a c1 ↔  Clause.Sat a c2

/-!
Definitions of CNF formulae.
-/

/-- A CNF formula is a list of clauses. -/
abbrev CNF (α : Type u) := List (Clause α)

/-- CNF f is satisfiable with an assignment a. -/
abbrev CNF.Sat (a : Assignment α) (f : CNF α) : Prop :=
  ∀ c ∈ f, Clause.Sat a c

/-- CNF f is unsatisfiable. -/
abbrev CNF.Unsat (f : CNF α) : Prop :=
  ∀ a : Assignment α, ¬ CNF.Sat a f

/-- The CNF f is a tautology. -/
abbrev CNF.Tautology (f : CNF α) : Prop :=
  ∀ a : Assignment α, CNF.Sat a f

/-- Equivalence of CNF formulea. -/
abbrev CNF.equiv (f1 f2 : CNF α) : Prop :=
  ∀ a : Assignment α, CNF.Sat a f1 ↔ CNF.Sat a f2

/-!
Theorems of literals.
-/

theorem Literal.eval_true_or_false (a : Assignment α) (x : Literal α) :
  x.eval a = true ∨ x.eval a = false := by
  exact Bool.eq_false_or_eq_true (eval a x)

theorem Literal.eq_negate_negate (x : Literal α) :
  x.negate.negate = x := by
  grind

theorem Literal.eval_negate (a : Assignment α) (x : Literal α) :
  x.negate.eval a = ! x.eval a := by
  unfold Literal.eval Literal.negate
  grind only [Bool.decide_eq_false]

/-!
Theorems of clauses.
-/

/-- Clause.equiv is commutative. -/
theorem Clause.equiv_comm (c1 c2 : Clause α) :
  Clause.equiv c1 c2 ↔ Clause.equiv c2 c1 := by
  unfold Clause.equiv
  aesop

/-- Clause.equiv is transitive. -/
theorem Clause.equiv_trans (c1 c2 c3 : Clause α) :
  Clause.equiv c1 c2 → Clause.equiv c2 c3 → Clause.equiv c1 c3 := by
  unfold Clause.equiv
  intros
  simp_all only

/-- The empty clause is unsatisfiable. -/
theorem Clause.unsat_of_empty (c : Clause α) (hc : c = []) :
  Clause.Unsat c := by
  rw [hc]
  unfold Clause.Unsat
  norm_num

/-- Clause c1 and c2 are equivalent if they are equal as sets, that is, c1 ⊆ c2 and c2 ⊆ c1. -/
theorem Clause.equiv_of_same_sets (c1 c2 : Clause α) :
  (c1 ⊆ c2) → (c2 ⊆ c1) → Clause.equiv c1 c2 := by
  intro hs12 hs21
  unfold Clause.equiv
  grind

/-- Clause c is a tautology if c contains both x and x.negate. -/
theorem Clause.tautology_of_complements (c : Clause α) (x : Literal α) :
  (x ∈ c) → (x.negate ∈ c) → Clause.Tautology c := by
  intro hx hnx
  unfold Clause.Tautology Clause.Sat
  intro a
  grind only [beq_false]

theorem Clause.sat_iff_contains_true_literal (a : Assignment α) (c : Clause α) :
  Clause.Sat a c ↔ ∃ x ∈ c, Literal.eval a x := by
  unfold Clause.Sat
  norm_num

/-!
Theorems of CNF formulae.
-/

/-- CNF.equiv is commutative. -/
theorem CNF.equiv_comm (f1 f2 : CNF α) :
  CNF.equiv f1 f2 ↔ CNF.equiv f2 f1 := by
  unfold CNF.equiv
  aesop

/-- CNF.equiv is transitive. -/
theorem CNF.equiv_trans (f1 f2 f3 : CNF α) :
  CNF.equiv f1 f2 → CNF.equiv f2 f3 → CNF.equiv f1 f3 := by
  unfold CNF.equiv
  intros
  simp_all only

/-- The empty clause is unsatisfiable. -/
theorem CNF.tautology_of_empty (f : CNF α) (hf : f = []) :
  CNF.Tautology f:= by
  rw [hf]
  unfold CNF.Tautology CNF.Sat
  norm_num

/-- CNF f is Unsat if f contains the empty clause. -/
theorem CNF.unsat_of_empty_clause (f : CNF α) (hf : [] ∈ f) :
  CNF.Unsat f := by
  unfold CNF.Unsat CNF.Sat
  grind

/-- CNF f is satisfiable if all clauses in f contain the same literal x. -/
theorem CNF.sat_of_same_literal (f : CNF α) (x : Literal α) :
  (∀ c, c ∈ f → x ∈ c) → (∃ a, CNF.Sat a f) := by
  intro hc
  let a : Assignment α := fun v => x.2
  use a
  unfold CNF.Sat
  grind

/-- CNF f is satisfiable if all clauses in f have a positive literal. -/
theorem CNF.sat_of_positive_literal (f : CNF α) :
  (∀ c, c ∈ f → (∃ x ∈ c, x.2 = true)) → (∃ a, CNF.Sat a f) := by
  intro hc
  let a : Assignment α := fun v => true
  use a
  unfold CNF.Sat
  grind

theorem CNF.sat_append_iff_sat_and (a : Assignment α) (f1 f2 : CNF α) :
  CNF.Sat a (f1 ++ f2) ↔ (CNF.Sat a f1 ∧ CNF.Sat a f2) := by
  unfold CNF.Sat
  exact List.forall_mem_append

theorem CNF.sat_flatmap_iff_sat_all (a : Assignment α) (fn : β → CNF α) (xs : List β) :
  CNF.Sat a (List.flatMap fn xs) ↔ ∀ x ∈ xs, CNF.Sat a (fn x) := by
  unfold CNF.Sat
  exact List.forall_mem_flatMap

theorem CNF.sat_map_iff_sat_clause_and_sat_map
  (a : Assignment α) (fn : β → Clause α) (x : β) (xs : List β) :
  CNF.Sat a (List.map fn (x :: xs)) ↔ Clause.Sat a (fn x) ∧ CNF.Sat a (List.map fn xs) := by
  unfold CNF.Sat
  norm_num

end SAT
end
