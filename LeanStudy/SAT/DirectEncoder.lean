/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.SAT.Basic

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

abbrev Card (a : Assignment α) (xs : List (Literal α)) : Nat :=
  List.countP (fun x => x.eval a) xs

theorem ALO.sat_iff_card_ge_one (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (ALO.encoder xs) ↔ Card a xs ≥ 1 := by
  unfold ALO.encoder
  constructor
  · unfold CNF.Sat
    norm_num
  · unfold CNF.Sat
    norm_num

lemma AMO.sat_of_card_le_one (a : Assignment α) (xs : List (Literal α)) :
  Card a xs ≤ 1 → CNF.Sat a (AMO.encoder xs) := by
  induction xs with
  | nil =>
    tauto
  | cons x1 xs1 ih =>
    intro h
    unfold AMO.encoder
    rw [CNF.sat_append_iff_sat_and]
    constructor
    · have : x1.eval a = true ∨ x1.eval a = false := by
        exact Literal.eval_true_or_false a x1
      obtain hx1t | hx1f := this
      case _ =>
        have : Card a xs1 = 0 := by simp_all
        have : ∀ y ∈ xs1, y.eval a = false := by simp_all
        unfold CNF.Sat
        aesop
      case _ =>
        unfold CNF.Sat Clause.Sat
        intro c hc
        use x1.negate
        constructor
        · grind
        · rw [Literal.eval_negate]
          simp_all
    · have : Card a xs1 ≤ 1 := by grind
      exact ih this

theorem AMO.sat_iff_card_le_one (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (AMO.encoder xs) ↔ Card a xs ≤ 1 := by
  constructor
  · induction xs with
    | nil =>
      norm_num
    | cons x1 xs1 ih =>
      intro h
      unfold AMO.encoder at h
      rw [CNF.sat_append_iff_sat_and] at h
      obtain ⟨ h1, h2 ⟩ := h
      have ih := ih h2
      have : x1.eval a = true ∨ x1.eval a = false := by
        exact Literal.eval_true_or_false a x1
      obtain hx1t | hx1f := this
      case _ =>
        unfold CNF.Sat at h1
        have : ∀ y ∈ xs1, y.eval a = false := by
          intro y hy
          have h1 := h1 [x1.negate, y.negate]
          have : Clause.Sat a [x1.negate, y.negate] := by
            apply h1
            simp_all
          grind
        simp_all
      case _ =>
        simp_all
  · exact (AMO.sat_of_card_le_one a xs)

theorem EXO_iff_card_eq_onee (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (EXO.encoder xs) ↔ Card a xs = 1 := by
  unfold EXO.encoder
  rw [CNF.sat_append_iff_sat_and]
  rw [ALO.sat_iff_card_ge_one]
  rw [AMO.sat_iff_card_le_one]
  exact antisymm_iff

/-
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
-/

end DirectEncoder

end
