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

lemma amo_nil :
  at_most_one ([] : List (Literal α)) = [] := by trivial

lemma amo_pairs (xs : List (Literal α)) (x y : Literal α)
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  [x.negate, y.negate] ∈ (at_most_one xs) ∨ [y.negate, x.negate] ∈ (at_most_one xs) := by
  have : (x, y) ∈ (Util.combinations2 xs) ∨ (y, x) ∈ (Util.combinations2 xs) :=
    Util.comb2_pair xs x y hx hy hxy
  grind [= at_most_one]

theorem amo_exists_no_two (xs : List (Literal α)) (a : Assignment α) :
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

theorem amo_iff_exists_no_two (xs : List (Literal α)) (a : Assignment α) (hxs : List.Nodup xs):
  CNF.Sat a (at_most_one xs) ↔
  (∀ x ∈ xs, x.eval a = false) ∨ (∃! x ∈ xs, x.eval a = true) := by

  have : (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → (x.eval a = false ∨ y.eval a = false)) →
    (∀ x ∈ xs, x.eval a = false) ∨ (∃! x ∈ xs, x.eval a = true) := by
    unfold Literal.eval
    intro h
    by_contra
    norm_num at this
    obtain ⟨ h1, h2 ⟩ := this
    obtain ⟨ v, hv ⟩ := h1
    have : (v, false) ∈ xs ∨ (v, true) ∈ xs := by tauto
    obtain hv1 | hv2 := this
    case _ =>
      have h := h (v, false) hv1
      sorry
    case _ =>
      sorry

    sorry

  induction xs with
  | nil =>
    bound
  | cons x1 xs1 ih1 =>
    induction xs1 with
    | nil =>
      unfold at_most_one Util.combinations2 Util.combinations2.f Util.combinations2
      simp [*] at *
      have : (x1.eval a) = true ∨ (x1.eval a) = false := by
        exact Bool.eq_false_or_eq_true (Literal.eval a x1)
      unfold Literal.eval at this
      simp at this
      obtain hx1 | hx2 := this
      case _ =>
        apply Or.inr
        use x1
        simp_all only [and_self, implies_true]
      case _ =>
        apply Or.inl
        assumption
    | cons x2 xs2 ih2 =>
      have : x1 ≠ x2 := by
        simp only [List.nodup_cons, List.mem_cons, not_or] at hxs
        exact hxs.left.left
      constructor
      · intro h
        let xs := x1 :: x2 :: xs2
        have : x1 ∈ xs := by tauto
        have : x2 ∈ xs := by tauto
        have : x1.eval a = false ∨ x2.eval a = false := by
          apply amo_exists_no_two xs a at h
          have h := h x1 ‹x1 ∈ xs› x2 ‹x2 ∈ xs› ‹x1 ≠ x2›
          assumption
        simp_all?
        sorry
      · sorry


  constructor
  · intro h
    apply amo_exists_no_two xs a at h
    induction xs with
    | nil =>
      norm_num
    | cons x1 xs1 ih1 =>
      have h := h x1
      induction xs1 with
      | nil =>
        simp_all only [List.not_mem_nil, ne_eq, decide_eq_false_iff_not, forall_const, isEmpty_prod,
          not_isEmpty_of_nonempty, or_true, IsEmpty.forall_iff, implies_true, decide_eq_true_eq,
          false_and, existsUnique_false, or_false, List.mem_cons, not_true_eq_false,
          or_self, forall_eq]
        have : a x1.1 = true ∨ a x1.1 = false := by norm_num
        obtain hx1 | hx2 := this
        case _ =>
          rw [hx1]
          simp only [Bool.true_eq, Bool.not_eq_true]
          sorry
        case _ =>
          sorry
      | cons x2 xs2 ih2 =>
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
