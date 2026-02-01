/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib

section

example (n : Nat) (hn : n % 6 = 0) : (n % 2 = 0) ∧ (n % 3 = 0) := by
  refine ⟨ ?_, ?_ ⟩
  -- constructor
  -- apply And.intro
  · show n % 2 = 0; omega
  · show n % 3 = 0; omega

example (n : Nat) (hn : n % 2 = 0 ∧ n % 3 = 0) : n % 6 = 0 := by
  have ⟨ hn1, hn2 ⟩ := hn
  -- rcases hn with ⟨ hn1, hn2 ⟩
  -- obtain ⟨ hn1, hn2 ⟩ := hn
  omega

example (n : Nat) (hn : n % 2 = 1) : (n % 4 = 1) ∨ (n % 4 = 3) := by
  by_contra
  simp_all only [not_or]
  omega

example (n : Nat) (hn : n % 2 = 1) : (n % 4 = 1) ∨ (n % 4 = 3) := by
  contrapose hn
  simp_all only [not_or]
  have ⟨ hn1, hn2 ⟩ := hn
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
