/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.Int.Range
import LeanStudy.SAT.Basic

section

namespace DirectEncoder

open SAT

def ALO.encode (xs : List (Literal α)) : CNF α :=
  [xs]

def AMO.encode : List (Literal α) → CNF α
  | [] => []
  | x :: xs =>
    xs.map (fun x1 => [x.negate, x1.negate]) ++
    AMO.encode xs

def EXO.encode (xs : List (Literal α)) : CNF α :=
  ALO.encode xs ++ AMO.encode xs

abbrev Card (a : Assignment α) (xs : List (Literal α)) : Nat :=
  List.countP (fun x => x.eval a) xs

theorem ALO.sat_iff_card_ge_one (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (ALO.encode xs) ↔ Card a xs ≥ 1 := by
  unfold ALO.encode
  constructor
  · unfold CNF.Sat
    norm_num
  · unfold CNF.Sat
    norm_num

theorem ALO.sat_iff_exists_true (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (ALO.encode xs) ↔ ∃ x ∈ xs, x.eval a = true := by
  rw [ALO.sat_iff_card_ge_one]
  norm_num

lemma AMO.sat_of_card_le_one (a : Assignment α) (xs : List (Literal α)) :
  Card a xs ≤ 1 → CNF.Sat a (AMO.encode xs) := by
  induction xs with
  | nil =>
    tauto
  | cons x1 xs1 ih =>
    intro h
    unfold AMO.encode
    rw [CNF.sat_append_iff_sat_and]
    constructor
    · have : x1.eval a = true ∨ x1.eval a = false := by
        exact Bool.eq_false_or_eq_true (Literal.eval a x1)
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
  CNF.Sat a (AMO.encode xs) ↔ Card a xs ≤ 1 := by
  constructor
  · induction xs with
    | nil =>
      norm_num
    | cons x1 xs1 ih =>
      intro h
      unfold AMO.encode at h
      rw [CNF.sat_append_iff_sat_and] at h
      obtain ⟨ h1, h2 ⟩ := h
      have ih := ih h2
      have : x1.eval a = true ∨ x1.eval a = false := by
        exact Bool.eq_false_or_eq_true (Literal.eval a x1)
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

theorem EXO.sat_iff_card_eq_one (a : Assignment α) (xs : List (Literal α)) :
  CNF.Sat a (EXO.encode xs) ↔ Card a xs = 1 := by
  unfold EXO.encode
  rw [CNF.sat_append_iff_sat_and]
  rw [ALO.sat_iff_card_ge_one]
  rw [AMO.sat_iff_card_le_one]
  exact antisymm_iff

end DirectEncoder

end
