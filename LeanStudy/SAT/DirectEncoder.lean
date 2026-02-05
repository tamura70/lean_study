/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic
import LeanStudy.SAT.Basic
import LeanStudy.SAT.Graph
import LeanStudy.Util

section

open SAT

namespace DirectEncoder

def at_least_one (xs : List (Literal α)) : CNF α :=
  [xs]

def at_most_one (xs : List (Literal α)) : CNF α :=
  (Util.combinations2 xs).map (fun (x1, x2) => [x1.negate, x2.negate])

def exact_one (xs : List (Literal α)) : CNF α :=
  at_least_one xs ++ at_most_one xs

#eval at_least_one ([1, 2, 3].map (fun i => (i, true)))
#eval at_most_one ([1, 2, 3].map (fun i => (i, true)))

theorem alo_iff_exists (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (at_least_one xs) ↔ ∃ x ∈ xs, x.eval a := by
  unfold at_least_one
  constructor
  · unfold CNF.Sat CNF.eval
    intro h
    unfold Clause.eval at h
    grind
  · unfold CNF.Sat CNF.eval
    intro h
    unfold Clause.eval
    grind

lemma amo_pairs (xs : List (Literal α)) (x y : Literal α)
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  [x.negate, y.negate] ∈ (at_most_one xs) ∨ [y.negate, x.negate] ∈ (at_most_one xs) := by
  have : (x, y) ∈ (Util.combinations2 xs) ∨ (y, x) ∈ (Util.combinations2 xs) :=
    Util.comb2_pair xs x y hx hy hxy
  grind [= at_most_one]

theorem amo_iff_exists_no_two (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (at_most_one xs) ↔
  (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → (x.eval a = false ∨ y.eval a = false)) := by
  constructor
  · intro h
    unfold CNF.Sat at h
    intros x hx y hy hxy
    obtain hxy1 | hxy2 := amo_pairs xs x y hx hy hxy
    case _ =>
      grind
    case _ =>
      grind
  · intro h
    unfold CNF.Sat
    rw [CNF.eval_equiv_forall]
    intros c hc
    unfold Clause.eval
    rw [Clause.eval_equiv_exists]



    have : (∀ c ∈ (at_most_one xs), Clause.eval a c) → (CNF.eval a (at_most_one xs)) := by
      intros
      unfold CNF.eval
      simp_all only [ne_eq, Prod.forall, Bool.forall_bool, Prod.mk.injEq, not_and,
        Bool.not_eq_false, Bool.not_eq_true, Bool.false_eq_true, imp_false, implies_true,
        forall_const, Bool.true_eq_false, List.all_eq_true]
    apply this
    try?
    by_contra
    simp only [Bool.not_eq_true] at this
    have : ∀ c ∈ (at_most_one xs), Clause.eval a c = false := by
      intros c hc
      have := this c
      hint
      sorry
    obtain := this
    sorry

theorem exo_unique (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (exact_one xs) → ∃! x ∈ xs, a x.1 = true := by
  sorry

def GraphColoring (G : Graph V) (c : Nat) : CNF (V × Nat) :=
  let cnf1 : CNF (V × Nat) :=
    G.vertices.flatMap
    fun v =>
      let xs := (List.range c).map (fun k => ((v, k), true))
      exact_one xs
  let cnf2 :=
    G.edges.flatMap
    (fun (u, v) =>
      (List.range c).map
      (fun k => [((u, k), false), ((v, k), false)])
    )
  cnf1 ++ cnf2

example (G : Graph V) (color : Nat) :
  Graph.Colorable G color → ∃ a, CNF.Sat a (GraphColoring G color) := by
  unfold Graph.Colorable Graph.Coloring
  intro hg
  obtain ⟨coloring, ⟨hcol1, hcol2⟩⟩ := hg
  let a : Assignment _ := fun (v,k) => coloring v = k
  use a
  unfold GraphColoring
  simp only
  rw [CNF.sat_concat]
  repeat rw [CNF.sat_flatMap]
  constructor
  · intros v hv
    unfold exact_one
    rw [CNF.sat_concat]
    constructor
    · unfold at_least_one

      sorry
    · sorry
    -- simp only [List.cons_append, List.nil_append]
  · sorry

end DirectEncoder

end
