/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
-- import Mathlib.Tactic
import LeanStudy.SAT.Basic

namespace SAT

/-- 3CNF -/
abbrev CNF.three (f : CNF α) : Prop :=
  ∀ c ∈ f, c.length ≤ 3

/-!
Theorems of Satisfiability Equivalence
-/

/-- Satisfiability preserving mapping. -/
def CNF.sat_preserving (t : CNF α → CNF β) (ta : (α → Bool) → (β → Bool)) :=
  ∀ f, (∀ a, (CNF.Sat a f) → (CNF.Sat (ta a) (t f))) ∧ ((CNF.Unsat f) → (CNF.Unsat (t f)))

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

theorem Literal.succ_ne_0 (x : Literal (Fin n)) :
  (Literal.succ x).1 ≠ 0 := by
  exact Ne.symm (not_eq_of_beq_eq_false rfl)

theorem Clause.succ_ne_0 (c : Clause (Fin n)) :
  ∀ x ∈ Clause.succ c, ∃ x1 ∈ c, x = Literal.succ x1 := by
  grind [= eq_def, = Literal.eq_def, = succ.eq_def]

theorem Literal.in_clause_succ (x : Literal (Fin n)) (c : Clause (Fin n)) :
  (x ∈ c) ↔ (Literal.succ x ∈ Clause.succ c) := by
  unfold Clause.succ Literal.succ
  norm_num

theorem Literal.eval_succ (a : Assignment (Fin n)) (x : Literal (Fin n)) :
  (Literal.eval a x = true) ↔ (Literal.eval (Assignment.succ a) (Literal.succ x) = true) := by
  unfold Assignment.succ
  trivial

theorem Clause.sat_literal (a : Assignment (Fin n)) (c : Clause (Fin n)) :
  Clause.Sat a c ↔ ∃ x ∈ c, (Literal.eval a x = true) := by
  unfold Clause.Sat Clause.eval
  norm_num

theorem Clause.sat_equiv_succ (a : Assignment (Fin n)) (c : Clause (Fin n)) :
  Clause.Sat a c ↔ Clause.Sat (Assignment.succ a) (Clause.succ c) := by
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
    apply Clause.succ_ne_0 at hx1
    obtain ⟨ x1, ⟨ hx1, hx2 ⟩ ⟩ := hx1
    use x1
    aesop

#check Function.update

end SAT
