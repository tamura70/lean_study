/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.List.Intervals
import Mathlib.Tactic.NormNum

namespace Util

abbrev range (n : Nat) : List Int :=
  (List.range n).map (fun k : Nat => ↑k)

abbrev IntRange' (s : Nat) (lb : Int) : List Int :=
  (range (s + 1)).map (fun k => lb + k)

abbrev IntRange (lb ub : Int) : List Int :=
  if ub < lb then [] else IntRange' (ub - lb).toNat lb

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

lemma range_inside (s : Nat) (k : Int) :
  k ∈ range (s + 1) ↔ 0 ≤ k ∧ k ≤ s := by
  unfold range
  constructor
  · intro h
    simp_all only [List.mem_map, List.mem_range]
    omega
  · intro h
    simp_all only [List.mem_map, List.mem_range]
    use k.toNat
    omega

lemma range_outside (s : Nat) (k : Int) :
  k ∉ range (s + 1) ↔ k < 0 ∨ s < k := by
  rw [range_inside]
  omega

lemma count_range_eq_zero (s : Nat) (k : Int) (h : k < 0 ∨ s < k) :
  List.count k (range (s + 1)) = 0 := by
  have : k ∉ range (s + 1) := by
    rw [range_outside]
    gcongr
  exact List.count_eq_zero.mpr this

lemma count_range_eq_one (s : Nat) (k : Int) (h : 0 ≤ k ∧ k ≤ s) :
  List.count k (range (s + 1)) = 1 := by
  set k1 := k.toNat
  have : k1 = k := by omega
  set xs := List.range (s + 1)
  set f : Nat → Int := fun k => ↑k
  have hf : Function.Injective f := by exact CharZero.cast_injective
  have h : List.count (f k1) (xs.map f) = List.count k1 xs := by
    exact count_injective k1 xs f hf
  have : f k1 = k := by gcongr
  rw [this] at h
  have : range (s + 1) = xs.map f := by
    unfold range
    gcongr
  rw [this]
  rw [h]
  grind

lemma count_intrange'_eq_count_range (s : Nat) (lb : Int) (i : Int) :
  List.count i (IntRange' s lb) = List.count (i - lb) (range (s + 1)) := by
  unfold IntRange' List.count
  set xs := range (s + 1)
  set f := fun k => lb + k
  set p := fun k => f k == i
  set q := fun i1 => i1 == i
  have : List.countP q (xs.map f) = List.countP p xs := by
    aesop
  rw [this]
  grind

lemma count_intrange'_eq_zero (s : Nat) (lb : Int) (i : Int) (h : i < lb ∨ lb + s < i) :
  List.count i (IntRange' s lb) = 0 := by
  rw [count_intrange'_eq_count_range s lb i]
  rw [count_range_eq_zero]
  omega

lemma count_intrange'_eq_one (s : Nat) (lb : Int) (i : Int) (h : lb ≤ i ∧ i ≤ lb + s) :
  List.count i (IntRange' s lb) = 1 := by
  rw [count_intrange'_eq_count_range s lb i]
  rw [count_range_eq_one]
  omega

lemma count_intrange_eq_count_intrange' (lb ub : Int) (i : Int) (h : lb ≤ ub) :
  List.count i (IntRange lb ub) = List.count i (IntRange' (ub - lb).toNat lb) := by
  grind

theorem count_intrange_eq_zero (lb ub : Int) (i : Int) (h : i < lb ∨ ub < i) :
  List.count i (IntRange lb ub) = 0 := by
  have : ub < lb ∨ lb ≤ ub := by exact Int.lt_or_le ub lb
  obtain h1 | h2 := this
  case _ =>
    unfold IntRange
    simp_all only [↓reduceIte, List.count_nil]
  case _ =>
    rw [count_intrange_eq_count_intrange' lb ub i h2]
    set s := (ub - lb).toNat
    have : ub = lb + s := by omega
    rw [this] at h
    exact count_intrange'_eq_zero s lb i h

theorem count_intrange_eq_one (lb ub : Int) (i : Int) (h : lb ≤ i ∧ i ≤ ub) :
  List.count i (IntRange lb ub) = 1 := by
  have : lb ≤ ub := by omega
  rw [count_intrange_eq_count_intrange' lb ub i this]
  set s := (ub - lb).toNat
  have : ub = lb + s := by omega
  rw [this] at h
  exact count_intrange'_eq_one s lb i h

end Util
