/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.List.Intervals
import Mathlib.Tactic.NormNum

namespace Util

abbrev IntRange (lb ub : Int) : List Int :=
  (List.range (ub - lb + 1).toNat).attach.map (fun k => ↑k + lb)

#eval IntRange (-1 : Int) (5 : Int)

lemma intrange_bound' (lb ub : Int) :
  ∀ i ∈ (IntRange lb ub), lb ≤ i ∧ i ≤ ub := by
  intro i hi
  grind

theorem intrange_bound (lb ub : Int) :
  ∀ i : Int, i ∈ (IntRange lb ub) ↔ lb ≤ i ∧ i ≤ ub := by
  intro i
  constructor
  · intro h
    exact intrange_bound' lb ub i h
  · intro ⟨ h1, h2 ⟩
    unfold IntRange
    simp only [List.mem_range, Int.lt_toNat, List.map_subtype, List.unattach_attach, List.mem_map]
    use (i - lb).toNat
    omega

theorem count_intrange_eq_one (lb ub i : Int) (h1 : lb ≤ i) (h2 : i ≤ ub) :
  List.count i (IntRange lb ub) = 1 := by
  unfold IntRange
  set di := (i - lb).toNat
  set r := List.range (ub - lb + 1).toNat
  have : List.count di r = 1 := by grind
  unfold List.count at *
  simp only [List.map_subtype, List.unattach_attach, List.countP_map]
  let p : Int → Bool := (fun x => x == i) ∘ (fun x => ↑x + lb)
  let q : Int → Bool := (fun x => x == di)
  have : ∀ x ∈ r, (p x = true) ↔ (q x = true) := by grind
  rw [List.countP_congr this]
  gcongr

theorem count_intrange_eq_zero (lb ub i : Int) (h : i < lb ∨ ub < i) :
  List.count i (IntRange lb ub) = 0 := by
  have : i ∉ (IntRange lb ub) := by grind
  exact List.count_eq_zero.mpr this

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
