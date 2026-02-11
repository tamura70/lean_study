/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.List.Intervals
import Mathlib.Tactic.NormNum

namespace Util

abbrev Range (lb ub : Nat) : List Nat :=
  (List.range (ub - lb + 1)).map (fun i => i + lb)

#eval Range (2 : Nat) (5 : Nat)

theorem range_bound (lb ub : Nat) :
  ∀ i, i ∈ (Range lb ub) ↔ lb ≤ i ∧ i ≤ ub := by
  intro i
  sorry

theorem count_injective [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
  (x : α) (xs : List α) (f : α → β) (hf : Function.Injective f) :
  (List.count (f x) (xs.map f)) = (List.count x xs) := by
  unfold List.count
  norm_num
  let p := (fun y : β => y == f x) ∘ f
  let q := (fun x1 : α => x1 == x)
  have : ∀ x ∈ xs, (p x = true) ↔ (q x = true) := by grind
  exact List.countP_congr this

theorem countP_congr_map [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
  (xs : List α) (f : α → β) (p : α → Bool) (q : β → Bool)
  (hpq : ∀ x : α, q (f x) = true ↔ (p x = true)) :
  List.countP q (xs.map f) = List.countP p xs := by
  have : List.countP q (xs.map f) = List.countP (fun x => q (f x)) xs := by
    simp only [List.countP_map]
    trivial
  rw [this]
  have : ∀ x ∈ xs, (q (f x) = true) ↔ (p x = true) := by
    intro x hx
    simp_all only [Bool.coe_iff_coe, List.countP_map]
  exact List.countP_congr this

theorem countP_map (xs : List α) (f : α → β) (p : β → Bool) :
  (List.countP p (xs.map f)) = (List.countP (fun x => p (f x)) xs) := by
  aesop

end Util
