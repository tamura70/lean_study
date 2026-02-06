/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Logic.ExistsUnique
import Mathlib.Tactic
import LeanStudy.SAT.Basic
import LeanStudy.SAT.Graph
import LeanStudy.Util

section

open SAT

namespace DirectEncoder

def at_least_one (xs : List (Literal α)) : CNF α :=
  [xs]

/-
def at_most_one' (xs : List (Literal α)) : CNF α :=
  (Util.combinations2 xs).map (fun (x1, x2) => [x1.negate, x2.negate])
-/

def at_most_one : List (Literal α) → CNF α
  | [] => []
  | x :: xs =>
    xs.map (fun x1 => [x.negate, x1.negate]) ++
    at_most_one xs

def exact_one (xs : List (Literal α)) : CNF α :=
  at_least_one xs ++ at_most_one xs

#eval at_least_one ([1, 2, 3].map (fun i => (i, true)))
#eval at_most_one ([1, 2, 3].map (fun i => (i, true)))

theorem ALO_iff_exists (xs : List (Literal α)) (a : Assignment α) :
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

lemma amo_nil :
  at_most_one ([] : List (Literal α)) = [] := by trivial

lemma amo_pairs (xs : List (Literal α)) (x y : Literal α)
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  [x.negate, y.negate] ∈ (at_most_one xs) ∨ [y.negate, x.negate] ∈ (at_most_one xs) := by
  have : (x, y) ∈ (Util.combinations2 xs) ∨ (y, x) ∈ (Util.combinations2 xs) :=
    Util.comb2_pair xs x y hx hy hxy
  hint
  sorry

lemma amo_exists_no_two (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (at_most_one xs) →
  (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → (x.eval a = false ∨ y.eval a = false)) := by
  intro h
  unfold CNF.Sat at h
  intros x hx y hy hxy
  obtain hxy1 | hxy2 := amo_pairs xs x y hx hy hxy
  case _ =>
    grind
  case _ =>
    grind

abbrev amo_propagation (xs : List (Literal α)) (a : Assignment α) :=
  ∀ x ∈ xs, Literal.eval a x = true → (∀ y ∈ xs, x ≠ y → y.eval a = false)

lemma amo_propagation_of_sat (xs : List (Literal α)) (a : Assignment α) :
  (CNF.Sat a (at_most_one xs)) → amo_propagation xs a := by
  intro h
  unfold amo_propagation
  intro x hx1 hx2
  have := amo_exists_no_two xs a h x hx1
  simp_all

/-
lemma amo_some_pair (xs : List (Literal α)) (hxs : List.Nodup xs)  (a : Assignment α) (c : Clause α) :
  c ∈ (at_most_one xs) → ∃ x, ∃ y, x ∈ xs ∧ y ∈ xs ∧ x ≠ y ∧ c = [x.negate, y.negate] := by
  unfold at_most_one
  intro h
  have := Util.comb2_some_pair xs hxs
  sorry

lemma amo_some_negative (xs : List (Literal α)) (a : Assignment α) (c : Clause α) :
  c ∈ (at_most_one xs) → ∃ x ∈ xs, x.negate ∈ c := by
  unfold at_most_one
  intro h
  induction xs with
  | nil =>
      trivial
  | cons x1 xs1 ih =>
      use x1
      unfold Util.combinations2 at h

      simp?
      sorry
-/

lemma amo_of_zero (xs : List (Literal α)) (a : Assignment α) :
  (∀ x ∈ xs, x.eval a = false) → CNF.Sat a (at_most_one xs) := by
  intro h
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih1 =>
    have ih1 : CNF.Sat a (at_most_one xs1) := by simp_all
    unfold at_most_one
    rw [CNF.sat_concat]
    constructor
    · aesop
    · assumption

lemma amo_of_one (xs : List (Literal α)) (hxs : List.Nodup xs) (a : Assignment α) :
  (∃! x ∈ xs, x.eval a = true) → CNF.Sat a (at_most_one xs) := by
  intro h
  obtain ⟨ x, ⟨ h1, h2 ⟩, h3 ⟩ := h
  have : ∀ y ∈ xs, x ≠ y → y.eval a = false := by grind
  unfold CNF.Sat
  rw [CNF.eval_equiv_forall]
  intro c hc
  sorry

theorem AMO_iff_all_false_or_uniq (xs : List (Literal α)) (hxs : List.Nodup xs) (a : Assignment α) :
  CNF.Sat a (at_most_one xs) ↔
  (∀ x ∈ xs, x.eval a = false) ∨ (∃! x ∈ xs, x.eval a = true) := by
  constructor
  · intro h
    have : (∀ x ∈ xs, x.eval a = false) ∨ (∃ x ∈ xs, x.eval a = true) := by grind
    obtain h1 | h2 := this
    case _ =>
      apply Or.inl
      assumption
    case _ =>
      apply Or.inr
      obtain ⟨ x, hx1, hx2 ⟩ := h2
      use x
      have hp := (amo_propagation_of_sat xs a h) x hx1 hx2
      grind
  · intro h
    obtain h1 | h2 := h
    case _ =>
      apply amo_of_zero
      assumption
    case _ =>
      apply amo_of_one xs hxs a
      assumption

theorem EXO_iff_unique (xs : List (Literal α)) (hxs : List.Nodup xs) (a : Assignment α) :
  CNF.Sat a (exact_one xs) ↔ ∃! x ∈ xs, x.eval a = true := by
  unfold exact_one
  rw [CNF.sat_concat]
  constructor
  · intro h
    obtain ⟨ h1, h2 ⟩ := h
    apply (ALO_iff_exists xs a).mp at h1
    apply (AMO_iff_all_false_or_uniq xs hxs a).mp at h2
    obtain h2z | h2o := h2
    case _ =>
      grind
    case _ =>
      gcongr
  · intro h
    and_intros
    · apply (ALO_iff_exists xs a).mpr
      exact ExistsUnique.exists h
    · apply (AMO_iff_all_false_or_uniq xs hxs a).mpr
      simp_all



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

example (G : Graph V) (coloring : V → C) :
  Graph.Coloring G coloring ↔
  able G color → ∃ a, CNF.Sat a (GraphColoring G color) := by
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
