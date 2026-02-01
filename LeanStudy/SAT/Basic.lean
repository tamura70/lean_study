/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic.NormNum

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
def Literal.isPositive (x : Literal α) := x.2

/-- Complement of a literal. -/
def Literal.negate : Literal α → Literal α :=
  fun x => (x.1, !x.2)

/-- Returns the value of the literal x under the given assignment a. -/
def Literal.eval (a : Assignment α) (x : Literal α) : Bool :=
  (a x.1) = x.2

/-!
Definitions of clauses.
-/

/-- A clause is a list of literals. -/
abbrev Clause (α : Type u) := List (Literal α)

/-- Returns the value of the clause c under the given assignment a. -/
def Clause.eval (a : Assignment α) (c : Clause α) : Bool :=
  c.any (fun x => Literal.eval a x)

/-- Equivalence of clauses. -/
def Clause.equiv (c1 c2 : Clause α) : Prop :=
  ∀ (a : α → Bool), Clause.eval a c1 = Clause.eval a c2

/-- The clause c is satisfied by an assignment a. -/
def Clause.Sat (a : Assignment α) (c : Clause α) : Prop :=
  Clause.eval a c = true

/-- The clause c is unsatisfiable. -/
def Clause.Unsat (c : Clause α) : Prop :=
  ∀ a : Assignment α, Clause.eval a c = false

/-- The clause c is a tautology. -/
def Clause.Tautology (c : Clause α) : Prop :=
  ∀ (a : α → Bool), Clause.eval a c = true

/-!
Definitions of CNF formulae.
-/

/-- A CNF formula is a list of clauses. -/
abbrev CNF (α : Type u) := List (Clause α)

/-- 3CNF -/
def CNF.three (f : CNF α) := ∀ c ∈ f, c.length ≤ 3

/-- Returns the value of the CNF f under the given assignment a. -/
def CNF.eval (a : Assignment α) (f : CNF α) : Bool :=
  f.all (fun c => Clause.eval a c)

/-- Equivalence of CNF formulea. -/
def CNF.equiv (f1 f2 : CNF α) : Prop :=
  ∀ (a : α → Bool), CNF.eval a f1 = CNF.eval a f2

/-- CNF f is satisfiable with an assignment a. -/
def CNF.Sat (a : Assignment α) (f : CNF α) : Prop :=
  CNF.eval a f = true

/-- CNF f is unsatisfiable. -/
def CNF.Unsat (f : CNF α) : Prop :=
  ∀ a : Assignment α, CNF.eval a f = false

/-- The CNF f is a tautology. -/
def CNF.Tautology (f : CNF α) : Prop :=
  ∀ (a : α → Bool), CNF.eval a f = true

/-!
Theorems of clauses.
-/

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

/-- The empty clause is unsatisfiable. -/
theorem Clause.unsat_of_empty (c : Clause α)
  : c = [] → Clause.Unsat c := by
  intro hc
  rw [hc]
  unfold Clause.Unsat
  exact fun a ↦ Bool.eq_false_of_le_false fun a ↦ a

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
  unfold Clause.Tautology Clause.eval Literal.eval
  simp_all only [List.any_eq_true, decide_eq_true_eq, Prod.exists, exists_eq_right']
  intro a
  use x.1
  have : a x.1 = x.2 ∨ a x.1 = !x.2 := by
    exact Bool.eq_or_eq_not (a x.1) x.2
  aesop

/-!
Theorems of CNF formulae.
-/

/-- CNF.equiv is commutative. -/
theorem CNF.equiv_comm (f1 f2 : CNF α)
  : CNF.equiv f1 f2 ↔ CNF.equiv f2 f1 := by
  unfold CNF.equiv
  aesop

/-- CNF.equiv is transitive. -/
theorem CNF.equiv_trans (f1 f2 f3 : CNF α)
  : CNF.equiv f1 f2 → CNF.equiv f2 f3 → CNF.equiv f1 f3 := by
  unfold CNF.equiv
  intros
  simp_all only

/-- The empty clause is unsatisfiable. -/
theorem CNF.tautology_of_empty (f : CNF α)
  : f = [] → CNF.Tautology f:= by
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
  unfold Clause.eval Literal.eval
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
  unfold Clause.eval Literal.eval
  simp_all only [Prod.exists, exists_eq_right, Bool.true_eq, Bool.decide_eq_true, List.any_eq_true]

theorem CNF.sat_concat (a : α → Bool) (f1 f2 : CNF α)
  : (CNF.Sat a f1 ∧ CNF.Sat a f2) ↔ CNF.Sat a (f1 ++ f2) := by
  unfold CNF.Sat CNF.eval
  norm_num

/-!
Theorems of Satisfiability Equivalence
-/

/-- Satisfiability preserving mapping. -/
def CNF.sat_preserving (t : CNF α → CNF β) (ta : (α → Bool) → (β → Bool)) :=
  ∀ f, (∀ a, (CNF.Sat a f) → (CNF.Sat (ta a) (t f))) ∧ ((CNF.Unsat f) → (CNF.Unsat (t f)))

theorem CNF.unsat_rev_of_sat_preserving (t : CNF α → CNF β) (ta : (α → Bool) → (β → Bool))
  : (CNF.sat_preserving t ta) → (∀ f : CNF α, CNF.Unsat (t f) → CNF.Unsat f) := by
  unfold CNF.sat_preserving CNF.Unsat CNF.Sat
  grind

/-- Convert a literal of Fin n to a literal of Fin (n+1) by increasing variable number by 1. -/
def Literal.succ (x : Literal (Fin n)) : Literal (Fin (n + 1)) :=
  (x.1.succ, x.2)

def Literal.pred (x : Literal (Fin (n + 1))) (h : x.1 ≠ 0) : Literal (Fin n) :=
  (x.1.pred h, x.2)

/-- Convert a clause of Fin n to a clause of Fin (n+1) by increasing variable number by 1. -/
def Clause.succ (c : Clause (Fin n)) : Clause (Fin (n + 1)) :=
  c.map (fun x => Literal.succ x)

/-- Convert a CNF of Fin n to a CNF of Fin (n+1) by increasing variable number by 1. -/
def CNF.succ (f : CNF (Fin n)) : CNF (Fin (n + 1)) :=
  f.map (fun c => Clause.succ c)

def Assignment.succ (a : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun v : Fin (n + 1) => if h: v ≠ 0 then a (v.pred h) else true

theorem Literal.in_clause_succ (x : Literal (Fin n)) (c : Clause (Fin n))
  : (x ∈ c) ↔ (Literal.succ x ∈ Clause.succ c) := by
  unfold Clause.succ Literal.succ
  norm_num

theorem Literal.eval_succ (a : Assignment (Fin n)) (x : Literal (Fin n))
  : (Literal.eval a x = true) ↔ (Literal.eval (Assignment.succ a) (Literal.succ x) = true) := by
  unfold Assignment.succ
  trivial

theorem Clause.sat_literal (a : Assignment (Fin n)) (c : Clause (Fin n))
  : Clause.Sat a c ↔ ∃ x ∈ c, (Literal.eval a x = true) := by
  unfold Clause.Sat Clause.eval
  norm_num

theorem Clause.sat_equiv_succ (a : Assignment (Fin n)) (c : Clause (Fin n))
  : Clause.Sat a c ↔ Clause.Sat (Assignment.succ a) (Clause.succ c) := by
  repeat rw [Clause.sat_literal]
  constructor
  · intro h
    obtain ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := h
    use Literal.succ x
    constructor
    · exact (Literal.in_clause_succ x c).mp hx1
    · trivial
  · intro h
    obtain ⟨ x1, ⟨ hx1, hx2 ⟩ ⟩ := h
    sorry

#check Function.update

end SAT
