/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.List.Nodup
-- import Mathlib.Data.Finmap
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import LeanStudy.SAT.Basic
-- import Mathlib.Tactic.NormNum

section

namespace SAT

-- variable (α : Type) [DecidableEq α] [Hashable α]
abbrev α := String

/-
abbrev add_variable (v : α) (vs : List α) : List α :=
  if v ∈ vs then vs else v :: vs

abbrev add_variables (vs1 : List α) (vs : List α) : List α :=
  match vs1 with
  | [] => vs
  | v :: vs1 => add_variables vs1 (add_variable v vs)
-/

abbrev Clause.variables (c : Clause α) : List α :=
  (c.map (fun x => x.1)).eraseDups

abbrev CNF.variables (f : CNF α) : List α :=
  match f with
  | [] => []
  | c :: f => (c.variables ++ (CNF.variables f)).eraseDups

abbrev Clause.subst (x : Literal α) (c : Clause α) : Clause α :=
  c.removeAll [x.negate]

abbrev CNF.subst (x : Literal α) (f : CNF α) : CNF α :=
  match f with
  | [] => []
  | c :: f =>
    if c.contains x then
      CNF.subst x f
    else
      (c.subst x) :: (CNF.subst x f)

abbrev CNF.substOpt (x : Literal α) (f : CNF α) : Option (CNF α) :=
  let f1 := CNF.subst x f
  if [] ∈ f1 then none else some f1

#check CNF.subst

abbrev Assignment.extend (x : Literal α) (a : Assignment α) : Assignment α :=
  fun y => if x.1 = y then x.2 else a y

lemma cnf_sat_of_sat_subst' (x : Literal α) (f : CNF α) (a : Assignment α) (hax : x.eval a = true) :
  CNF.Sat a (f.subst x) → CNF.Sat a f := by
  induction f with
  | nil =>
    unfold CNF.subst CNF.Sat
    simp
  | cons c f' ih =>
    unfold CNF.subst CNF.Sat
    intro h c1 hc1
    let h1 := h c
    split at h1
    case isTrue hcx =>
      unfold CNF.Sat at ih
      grind
    case isFalse hcx =>
      set c2 := Clause.subst x c with hc2
      have hc2_sat : Clause.Sat a c2 := by
        apply (h c2)
        grind
      grind

lemma clause_sat_iff_sat_subst
  (x : Literal α) (c : Clause α) (a : Assignment α) (hax : x.eval a = true) :
  Clause.Sat a (c.subst x) ↔ Clause.Sat a c := by
  unfold Clause.Sat Clause.subst
  constructor
  · intro h
    obtain ⟨ x1, hx1 ⟩ := h
    use x1
    have : x1 ∈ c := by grind
    simp_all only [decide_eq_true_eq, and_self]
  · intro h
    obtain ⟨ x1, hx1 ⟩ := h
    by_cases x1 = x.negate
    case _ =>
      grind
    case _ =>
      grind

lemma sat_subst_of_cnf_sat'
  (x : Literal α) (f : CNF α) (a : Assignment α) (hax : x.eval a = true) :
  CNF.Sat a f → CNF.Sat a (f.subst x) := by
  intro h
  induction f with
  | nil =>
    unfold CNF.subst CNF.Sat
    simp
  | cons c f ih =>
    unfold CNF.subst CNF.Sat
    intro c' hc'
    split at hc'
    case isTrue hcx =>
      grind
    case isFalse hcx =>
      have hc_sat : Clause.Sat a c := by solve_by_elim
      have hf_sat : CNF.Sat a f := by solve_by_elim
      have hf'_sat : CNF.Sat a (CNF.subst x f) := ih hf_sat
      obtain hc'1 | hc'2 := hc'
      case _ =>
        exact (clause_sat_iff_sat_subst x c a hax).mpr hc_sat
      case _ =>
        solve_by_elim

lemma cnf_sat_of_sat_subst (x : Literal α) (f : CNF α) (a : Assignment α) :
  (x.eval a = true ∧ CNF.Sat a (f.subst x)) ∨
  (x.negate.eval a = true ∧ CNF.Sat a (f.subst x.negate)) →
  CNF.Sat a f := by
  intro h
  obtain ⟨ h11, h12 ⟩ | ⟨ h21, h22 ⟩ := h
  case _ =>
    exact cnf_sat_of_sat_subst' x f a h11 h12
  case _ =>
    exact cnf_sat_of_sat_subst' x.negate f a h21 h22

theorem cnf_sat_iff_sat_subst (x : Literal α) (f : CNF α) (a : Assignment α) :
  (x.eval a = true ∧ CNF.Sat a (f.subst x)) ∨
  (x.negate.eval a = true ∧ CNF.Sat a (f.subst x.negate)) ↔
  CNF.Sat a f := by
  constructor
  · exact fun a_1 ↦ cnf_sat_of_sat_subst x f a a_1
  · intro h
    by_cases x.eval a = true
    case _ h1 =>
      left
      constructor
      · assumption
      · exact sat_subst_of_cnf_sat' x f a h1 h
    case _ h2 =>
      right
      constructor
      · have : x.eval a = false := by simp [*]
        grind only [beq_false]
      · have h2 : x.negate.eval a = true := by
          unfold Literal.negate
          grind only [Prod.eq_iff_fst_eq_snd_eq, Prod.snd_eq_iff, Prod.mk_inj]
        exact sat_subst_of_cnf_sat' x.negate f a h2 h

def solver1 (f : CNF α) : Option (Std.HashMap α Bool) :=
  let rec search (vs : List α) (f: CNF α) : Option (Std.HashMap α Bool) :=
    let rec decide (v : α) (sign : Bool) (vs : List α) (f : CNF α) : Option (Std.HashMap α Bool) :=
      f.substOpt (v, sign) >>= fun g =>
      search vs g >>= fun a =>
      some (a.insert v sign)
    match vs with
    | [] => some {}
    | v :: vs => (decide v false vs f) <|> (decide v true vs f)
  search f.variables f


/-
abbrev Clause.finset_of_variables (c : Clause α) : Finset α :=
  (c.map (fun x => x.1)).toFinset

lemma clause_vars_as_finset (c : Clause α) :
  ∀ v, v ∈ c.variables ↔ v ∈ c.finset_of_variables := by
  sorry

abbrev CNF.finset_of_variables (f : CNF α) : Finset α :=
  (c.map (fun x => x.1)).toFinset

lemma cnf_vars_as_set (f : CNF α) :
  ∀ v, v ∈ f.variables ↔ ∃ c ∈ f, ∃ x ∈ c, v = x.1 := by
  unfold CNF.variables
  sorry


abbrev hashmap_to_assignment (map : Std.HashMap α Bool) : Assignment α :=
  fun (x : α) => map.getD x false

lemma cnf_novars_iff_clauses_novars (f : CNF α) :
  f.variables.isEmpty ↔ ∀ c ∈ f, c.variables.isEmpty := by
  unfold CNF.variables
  sorry
  constructor
  · intro h
    sorry
  · intro h
    sorry


lemma clauses_empty_of_variables_empty (f : CNF α) :
  f.variables.isEmpty → ∀ c ∈ f, c = [] := by
  unfold CNF.variables
  intro hf c hc
  refine Eq.symm (List.Perm.nil_eq ?_)
  sorry

lemma solver1_sat (f : CNF α) (sol : Std.HashMap α Bool) :
  solver1 f = some sol → CNF.Sat (hashmap_to_assignment sol) f := by
  unfold solver1 solver1.search
  split
  case h_1 h1 =>
    intro hs
    simp only [Option.some.injEq] at hs
    rw [← hs]
    unfold hashmap_to_assignment
    simp only [Std.HashMap.getD_empty]
    sorry
  case h_2 =>
    sorry
-/

end SAT
end

section

open SAT

def p : Literal α := ("p", true)
def q : Literal α := ("q", true)

def cnf1 : CNF α := [
  [p, q],
  [p.negate, q.negate]
]

#check cnf1
#eval cnf1.variables
#eval CNF.substOpt p cnf1
#eval solver1 cnf1





end
