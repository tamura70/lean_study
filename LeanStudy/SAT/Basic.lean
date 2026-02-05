/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic

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

/-- Returns the value of the clause c under the given assignment a. -/
abbrev Clause.eval (a : Assignment α) (c : Clause α) : Bool :=
  c.any (fun x => Literal.eval a x)

/-- The clause c is satisfied by an assignment a. -/
abbrev Clause.Sat (a : Assignment α) (c : Clause α) : Prop :=
  Clause.eval a c = true

/-- The clause c is unsatisfiable. -/
abbrev Clause.Unsat (c : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.eval a c = false

/-- The clause c is a tautology. -/
abbrev Clause.Tautology (c : Clause α) : Prop :=
  ∀ (a : α → Bool), Clause.eval a c = true

/-- Equivalence of clauses. -/
abbrev Clause.equiv (c1 c2 : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.eval a c1 = Clause.eval a c2

/-!
Definitions of CNF formulae.
-/

/-- A CNF formula is a list of clauses. -/
abbrev CNF (α : Type u) := List (Clause α)

/-- Returns the value of the CNF f under the given assignment a. -/
abbrev CNF.eval (a : Assignment α) (f : CNF α) : Bool :=
  f.all (fun c => Clause.eval a c)

/-- Equivalence of CNF formulea. -/
abbrev CNF.equiv (f1 f2 : CNF α) : Prop :=
  ∀ (a : α → Bool), CNF.eval a f1 = CNF.eval a f2

/-- CNF f is satisfiable with an assignment a. -/
abbrev CNF.Sat (a : Assignment α) (f : CNF α) : Prop :=
  CNF.eval a f = true

/-- CNF f is unsatisfiable. -/
abbrev CNF.Unsat (f : CNF α) : Prop :=
  ∀ a : Assignment α, CNF.eval a f = false

/-- The CNF f is a tautology. -/
abbrev CNF.Tautology (f : CNF α) : Prop :=
  ∀ (a : α → Bool), CNF.eval a f = true

/-!
Theorems of literals.
-/

theorem Literal.eval_negate (a : Assignment α) (x : Literal α) :
  Literal.eval a x.negate = ! Literal.eval a x := by
  unfold Literal.eval Literal.negate
  have : x.2 = true ∨ x.2 = false := by norm_num
  grind

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
theorem Clause.unsat_of_empty (c : Clause α) :
  c = [] → Clause.Unsat c := by
  intro hc
  rw [hc]
  unfold Clause.Unsat
  norm_num

/-- Clause c1 and c2 are equivalent if they are equal as sets, that is, c1 ⊆ c2 and c2 ⊆ c1. -/
theorem Clause.equiv_of_same_sets (c1 c2 : Clause α) :
  (c1 ⊆ c2) → (c2 ⊆ c1) → Clause.equiv c1 c2 := by
  intro hs12 hs21 a
  unfold Clause.eval
  grind

/-- Clause c is a tautology if c contains both x and x.negate. -/
theorem Clause.tautology_of_complements (c : Clause α) (x : Literal α) :
  (x ∈ c) → (x.negate ∈ c) → Clause.Tautology c := by
  intro hx hnx
  unfold Clause.Tautology Clause.eval Literal.eval
  simp_all only [List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right']
  intro a
  use x.1
  have : a x.1 = x.2 ∨ a x.1 = !x.2 := by
    exact Bool.eq_or_eq_not (a x.1) x.2
  aesop

@[simp]
theorem Clause.eval_equiv_exists (a : Assignment α) (c : Clause α) :
  Clause.eval a c ↔ ∃ x ∈ c, Literal.eval a x := by
  unfold Clause.eval
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
theorem CNF.tautology_of_empty (f : CNF α) :
  f = [] → CNF.Tautology f:= by
  intro hc
  rw [hc]
  unfold CNF.Tautology
  exact fun a ↦ (fun {b} ↦ Bool.eq_false_imp_eq_true.mp) (congrFun rfl)

/-- CNF f is Unsat if f contains the empty clause. -/
theorem CNF.unsat_of_empty_clause (f : CNF α) :
  [] ∈ f → Unsat f := by
  intro hf
  unfold Unsat CNF.eval
  aesop

/-- CNF f is satisfiable if all clauses in f contain the same literal x. -/
theorem CNF.sat_of_same_literal (f : CNF α) (x : Literal α) :
  (∀ c, c ∈ f → x ∈ c) → (∃ a, CNF.Sat a f) := by
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
  unfold Clause.eval Literal.eval
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right']
  use x.1
  rw [ha1]
  simp_all only [Prod.mk.eta]

/-- CNF f is satisfiable if all clauses in f have a positive literal. -/
theorem CNF.sat_of_positive_literal (f : CNF α) :
  (∀ c, c ∈ f → (∃ x ∈ c, x.2 = true)) → (∃ a, CNF.Sat a f) := by
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
  unfold Clause.eval Literal.eval
  simp_all only [Prod.exists, exists_eq_right, Bool.true_eq, Bool.decide_eq_true, List.any_eq_true]

@[simp]
theorem CNF.eval_equiv_forall (a : Assignment α) (f : CNF α) :
  CNF.eval a f ↔ ∀ c ∈ f, Clause.eval a c := by
  unfold CNF.eval
  norm_num

@[simp]
theorem CNF.sat_concat (a : α → Bool) (f1 f2 : CNF α) :
  CNF.Sat a (f1 ++ f2) ↔ (CNF.Sat a f1 ∧ CNF.Sat a f2) := by
  unfold CNF.Sat CNF.eval
  norm_num

@[simp]
theorem CNF.sat_flatMap (a : α → Bool) (fn : β → CNF α) (xs : List β) :
  CNF.Sat a (List.flatMap fn xs) ↔ ∀ x ∈ xs, CNF.Sat a (fn x) := by
  unfold CNF.Sat CNF.eval
  norm_num

@[simp]
theorem CNF.false_cnf_of_false_clause (a : α → Bool) (c : Clause α) (f : CNF α) (h : c ∈ f) :
  Clause.eval a c = false → CNF.eval a f = false := by
  intro hc
  unfold CNF.eval
  grind

@[simp]
theorem CNF.true_clause_of_true_cnf (a : α → Bool) (c : Clause α) (f : CNF α) (h : c ∈ f) :
  CNF.eval a f = true → Clause.eval a c = true := by
  intro h
  unfold CNF.eval at h
  grind

end SAT
