/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Tactic

section

theorem mod_eq {n m1 m2 r : Nat} (h1 : n % m1 = r) (h2 : m1 % m2 = 0) :
  (n % m2) = (r % m2) := by
  have : m2 ∣ m1 := Nat.dvd_of_mod_eq_zero h2
  have : n % m1 % m2 = n % m2 := Nat.mod_mod_of_dvd n this
  rw [← this]
  rw [h1]

example (n : Nat) (h : n % 6 = 0) : (n % 2 = 0) ∧ (n % 3 = 0) := by
  constructor
  -- apply And.intro
  · show n % 2 = 0
    rw [mod_eq h]
    trivial
  · show n % 3 = 0
    rw [mod_eq h]
    trivial

example (n : Nat) (h : n % 2 = 0 ∧ n % 3 = 0) : n % 6 = 0 := by
  obtain ⟨ h2, h3 ⟩ := h
  -- have ⟨ h2, h3 ⟩ := h
  -- rcases h with ⟨ h2, h3 ⟩
  have hd2 : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h2
  have hd3 : 3 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h3
  apply Nat.dvd_iff_mod_eq_zero.mp
  exact Nat.lcm_dvd hd2 hd3

example (n : Nat) (h : n % 2 = 1) : (n % 4 = 1) ∨ (n % 4 = 3) := by
  have h41 : (n % 2 = 1) → (n % 4 ≠ 3) → (n % 4 = 1) := by omega
  have h43 : (n % 2 = 1) → (n % 4 ≠ 1) → (n % 4 = 3) := by omega
  have h41 := h41 h
  have h43 := h43 h
  have : (n % 4 = 3) ∨ (n % 4 ≠ 3) := by exact eq_or_ne (n % 4) 3
  obtain h1 | h2 := this
  case _ =>
    apply Or.inr h1
  case _ =>
    sorry


  obtain h1 | h2 := this
  case _ =>
    apply Or.inl h1
  case _ =>
    apply Or.inr h2

example (n : Nat) (h : n % 2 = 1) : (n % 4 = 1) ∨ (n % 4 = 3) := by
  contrapose h
  simp_all only [not_or]
  obtain ⟨ h1, h2 ⟩ := h

  omega

example (n : Nat) (hn : (n % 4 = 1) ∨ (n % 4 = 3)) : (n % 2 = 1) := by
  rcases hn with hn1 | hn2
  case _ => omega
  case _ => omega

example (n : Nat) (hn : n % 2 = 0) : (n % 3 = 0) → (n % 6 = 0) := by
  intro hn1
  show n % 6 = 0
  omega

example (n : Nat) (hn : (n % 2 = 0) → (n % 3 = 0)) : (n % 2 = 1) ∨ (n % 6 = 0) := by
  contrapose hn
  simp_all only [not_or, Nat.mod_two_not_eq_one, forall_const]
  have ⟨ hn1, hn2 ⟩ := hn
  omega







end
