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

theorem amo_iff_exists_no_two' (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (at_most_one xs) →
  List.length (List.filter (fun x => x.eval a) xs) ≤ 1 := by
  contrapose
  simp only [gt_iff_lt, List.length_filter_pos_iff, Prod.exists, Bool.exists_bool, not_exists,
    not_or, not_and, Bool.not_eq_true]
  intro h


  unfold at_most_one
  unfold CNF.Sat CNF.eval
  norm_num
  unfold
  sorry

theorem amo_iff_exists_no_two (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (at_most_one xs) ↔
  (∀ x ∈ xs, ∀ y ∈ xs, x.eval a → y.eval a → x = y) := by
  -- unfold at_most_one
  constructor
  · intro h1
    intros x hx y hy hx1 hx2
    by_contra
    have : ∃ c ∈ at_most_one xs, x.negate ∈ c ∧ y.negate ∈ c := by
      unfold at_most_one
      sorry
    sorry
  · sorry

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
