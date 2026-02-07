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

def ALO.encoder (xs : List (Literal α)) : CNF α :=
  [xs]

def AMO.encoder : List (Literal α) → CNF α
  | [] => []
  | x :: xs =>
    xs.map (fun x1 => [x.negate, x1.negate]) ++
    AMO.encoder xs

def EXO.encoder (xs : List (Literal α)) : CNF α :=
  ALO.encoder xs ++ AMO.encoder xs

#eval ALO.encoder ([1, 2, 3].map (fun i => (i, true)))
#eval AMO.encoder ([1, 2, 3].map (fun i => (i, true)))

theorem ALO.sat_iff_exists_true_literal (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (ALO.encoder xs) ↔ ∃ x ∈ xs, x.eval a = true := by
  unfold ALO.encoder
  constructor
  · unfold CNF.Sat
    norm_num
  · unfold CNF.Sat
    norm_num

/-
lemma amo_nil :
  AMO.encoder ([] : List (Literal α)) = [] := by trivial

lemma amo_pairs (xs : List (Literal α)) (x y : Literal α)
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  [x.negate, y.negate] ∈ (AMO.encoder xs) ∨ [y.negate, x.negate] ∈ (AMO.encoder xs) := by
  have : (x, y) ∈ (Util.combinations2 xs) ∨ (y, x) ∈ (Util.combinations2 xs) :=
    Util.comb2_pair xs x y hx hy hxy
  grind [= AMO.encoder]
-/

/-
lemma amo_exists_no_two (xs : List (Literal α)) (a : Assignment α) :
  CNF.Sat a (AMO.encoder xs) →
  (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → (x.eval a = false ∨ y.eval a = false)) := by
  intro h
  unfold CNF.Sat at h
  intros x hx y hy hxy
  obtain hxy1 | hxy2 := amo_pairs xs x y hx hy hxy
  case _ =>
    grind
  case _ =>
    grind
-/

abbrev amo_propagation (xs : List (Literal α)) (a : Assignment α) :=
  ∀ x ∈ xs, Literal.eval a x = true → (∀ y ∈ xs, x ≠ y → y.eval a = false)

lemma amo_propagation_of_sat (xs : List (Literal α)) (a : Assignment α) :
  (CNF.Sat a (at_most_one xs)) → amo_propagation xs a := by
  intro h
  unfold amo_propagation
  intro x hx1 hx2
  have := amo_exists_no_two xs a h x hx1
  simp_all

lemma amo_of_zero (xs : List (Literal α)) (a : Assignment α) :
  (∀ x ∈ xs, x.eval a = false) → CNF.Sat a (at_most_one xs) := by
  intro h
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih1 =>
    have ih1 : CNF.Sat a (AMO.encoder xs1) := by simp_all
    unfold at_most_one
    rw [CNF.sat_concat]
    constructor
    · aesop
    · assumption

lemma amo_of_one (xs : List (Literal α)) (hxs : List.Nodup xs) (a : Assignment α) :
  (∃! x ∈ xs, x.eval a = true) → CNF.Sat a (AMO.encoder xs) := by
  intro h
  obtain ⟨ x, hx ⟩ := h
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih1 =>
    have : x = x1 ∨ x ≠ x1 := by exact eq_or_ne x x1
    obtain hx_eq_x1 | hx_ne_x1 := this
    case _ =>
      rw [hx_eq_x1] at hx
      have : ∀ y ∈ xs1, y.eval a = false := by grind
      have : CNF.Sat a (AMO.encoder xs1) := amo_of_zero xs1 a this
      unfold AMO.encoder
      rw [CNF.sat_concat]
      aesop
    case _ =>
      have : x1.negate.eval a = true := by
        rw [Literal.eval_negate a]
        grind
      have hcx1 : ∀ (c : Clause α), x1.negate ∈ c → Clause.eval a c = true := by
        intro c hc
        unfold Clause.eval
        have : (∃ x ∈ c, x.eval a = true) → ((List.any c (fun x => x.eval a)) = true) := by
          grind
        apply this
        use x1.negate
      have : CNF.Sat a (AMO.encoder xs1) := by grind
      unfold AMO.encoder
      rw [CNF.sat_concat]
      constructor
      · unfold CNF.Sat CNF.eval
        grind
      · assumption

theorem AMO_iff_all_false_or_uniq (xs : List (Literal α)) (hxs : List.Nodup xs) (a : Assignment α) :
  CNF.Sat a (AMO.encoder xs) ↔
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
  CNF.Sat a (EXO.encoder xs) ↔ ∃! x ∈ xs, x.eval a = true := by
  unfold EXO.encoder
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
      EXO.encoder xs
  let cnf2 :=
    G.edges.flatMap
    (fun (u, v) =>
      (List.range c).map
      (fun k => [((u, k), false), ((v, k), false)])
    )
  cnf1 ++ cnf2

example (G : Graph V) (coloring : V → Fin c) :
  Graph.Coloring G coloring → ∃ a, CNF.Sat a (GraphColoring G c) := by
  unfold Graph.Coloring
  sorry

end DirectEncoder

end
