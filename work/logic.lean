import Mathlib.Tactic

section

namespace Logic

variable {A B C : Prop}

/-! Assumption
Γ, A ⊢ A
-/
section
-- Term mode
example (Γ : Prop) (ha : A) : A :=
  ha

-- Tactic mode
example (Γ : Prop) (ha : A) : A := by
  exact ha

end

/-! Implication introduction
Γ, A ⊢ B
Γ ⊢ A → B
-/
section
-- Term mode
example (Γ : Prop) : A → B :=
  fun ha :A =>
  -- Proof of Γ, A ⊢ B
  sorry

example : A → B → A :=
  fun ha : A =>
  fun _ : B =>
  ha

-- Tactic mode
example (Γ : Prop) : A → B := by
  intro (ha : A)
  -- Proof of Γ, A ⊢ B
  sorry

example : A → B → A := by
  intro ha hb
  exact ha

end

/-! Implication elimination (application)
Γ, A, B ⊢ C
Γ, A, A → B ⊢ C
-/
section
-- Term mode
example (Γ : Prop) (ha : A) (hab : A → B) : C :=
  have hb : B := hab ha
  -- Proof of Γ, A, A → B, B ⊢ C
  sorry

example (hab : A → B) (hbc : B → C) : A → C :=
  fun ha : A =>
  have hb : B := hab ha
  have hc : C := hbc hb
  hc

example (hab : A → B) (hbc : B → C) : A → C :=
  fun ha : A =>
  have hb : B := hab ha
  hbc hb

example (hab : A → B) (hbc : B → C) : A → C :=
  fun ha : A =>
  hbc (hab ha)

-- Tactic mode
example (Γ : Prop) (ha : A) (hab : A → B) : C := by
  have hb : B := by apply hab ha
  -- Proof of Γ, A, A → B, B ⊢ C
  sorry

example (hab : A → B) (hbc : B → C) : A → C := by
  intro ha
  have hb := by apply hab ha
  exact hbc hb

example (hab : A → B) (hbc : B → C) : A → C := by
  intro ha
  exact hbc (hab ha)

theorem imp_elim (hab : A → B) (ha : A) (hbc : B → C) : C := by
  exact hbc (hab ha)

example (Γ : Prop) (hab : A → B) : C := by
  apply imp_elim hab
  · -- Proof of Γ ⊢ A
    sorry
  · intro hb
    -- Proof of Γ, B ⊢ C
    sorry

end

/-! Negation introduction
Γ, A ⊢ False
Γ ⊢ ¬ A
-/
section
-- Term mode
example (Γ : Prop) : ¬ A :=
  fun ha : A =>
  -- Proof of Γ, A ⊢ False
  sorry

example (hab : A → B) (hnb : ¬ B) : ¬ A :=
  fun ha : A =>
  hnb (hab ha)

-- Tactic mode
example (Γ : Prop) : ¬ A := by
  intro ha
  -- Proof of Γ, A ⊢ False
  sorry

example (hab : A → B) (hnb : ¬ B) : ¬ A := by
  intro ha
  exact hnb (hab ha)

end

/-! Negation elimination (application), False elimination
Γ, A, ¬ A ⊢ C
-/
section

-- Term mode
example (Γ : Prop) (ha : A) (hna : ¬ A) : C :=
  absurd ha hna

example (Γ : Prop) (ha : A) (hna : ¬ A) : C :=
  have hf := hna ha
  False.elim hf

theorem not_not_intro (ha : A) : ¬ ¬ A :=
  fun hna : ¬ A =>
  hna ha

example (hnnna : ¬ ¬ ¬ A) : ¬ A :=
  fun ha : A =>
  have hnna : ¬ ¬ A := not_not_intro ha
  hnnna hnna

example (hnna : ¬ ¬ A) : A :=
  have h : A ∨ ¬ A := Classical.em A
  Or.elim h
  (fun ha : A => ha)
  (fun hna : ¬ A => False.elim (hnna hna))

-- Tactic mode
example (Γ : Prop) (ha : A) (hna : ¬ A) : C := by
  contradiction

example (Γ : Prop) (ha : A) (hna : ¬ A) : C := by
  have hf : False := by apply hna ha
  contradiction

example (hnnna : ¬ ¬ ¬ A) : ¬ A := by
  intro ha
  have hnna : ¬ ¬ A := not_not_intro ha
  exact hnnna hnna

end

/-! And introduction
Γ ⊢ A   Γ ⊢ B
Γ ⊢ A ∧ B
-/
section
-- Term mode
example (Γ : Prop) : A ∧ B :=
  have ha : A :=
    -- Proof of Γ ⊢ A
    sorry
  have hb : B :=
    -- Proof of Γ ⊢ B
    sorry
  And.intro ha hb

-- Tactic mode
example (Γ : Prop) : A ∧ B := by
  apply And.intro
  · -- Proof of Γ ⊢ A
    sorry
  · -- Proof of Γ ⊢ B
    sorry

example (Γ : Prop) : A ∧ B := by
  constructor
  · -- Proof of Γ ⊢ A
    sorry
  · -- Proof of Γ ⊢ B
    sorry

end

/-! And elimination
Γ, A, B ⊢ C
Γ, A ∧ B ⊢ C
-/
section
-- Tactic mode
example (Γ : Prop) (hab : A ∧ B) : C := by
  have ha : A := by apply And.left hab
  have hb : B := by apply And.right hab
  -- Proof of Γ, A, B ⊢ C
  sorry

example (hab : A ∧ B) : B ∧ A := by
  constructor
  · exact And.right hab
  · exact And.left hab

example (hab : A ∧ B) : B ∧ A := by
  constructor
  · exact hab.right
  · exact hab.left

example (hab : A ∧ B) : B ∧ A := by
  exact And.intro hab.right hab.left

example (hab : A ∧ B) : B ∧ A := by
  exact ⟨ hab.right, hab.left ⟩

example (hab : A ∧ B) : B ∧ A := by
  obtain ⟨ ha, hb ⟩ := hab
  exact ⟨ hb, ha ⟩

example : A ∧ B → B ∧ A := by
  intro ⟨ ha, hb ⟩
  exact ⟨ hb, ha ⟩



end

/-! Or introduction
Γ ⊢ A   or   Γ ⊢ B
Γ ⊢ A ∨ B
-/
section
-- Tactic mode
example (Γ : Prop) : A ∨ B := by
  apply Or.inl
  -- Proof of Γ ⊢ A
  sorry

example (Γ : Prop) : A ∨ B := by
  apply Or.inr
  -- Proof of Γ ⊢ B
  sorry

end

/-! Or elimincation
Γ, A ⊢ C    Γ, B ⊢ C
Γ, A ∨ B ⊢ C
-/
section
-- Tactic mode
example (Γ : Prop) (hab : A ∨ B) : C := by
  apply Or.elim hab
  · -- Proof of Γ, A ⊢ C
    sorry
  · -- Proof of Γ, B ⊢ C
    sorry

example (hab : A ∨ B) : B ∨ A := by
  apply Or.elim hab
  · exact Or.inr
  · exact Or.inl

end

/-! Iff introduction
Γ ⊢ A → B   Γ ⊢ B → A
Γ ⊢ A ↔ B
-/
section
-- Tactic mode
example (Γ : Prop) : A ↔ B := by
  constructor
  · -- Proof of Γ ⊢ A → B
    sorry
  · -- Proof of Γ ⊢ B → A
    sorry

end

/-! Iff application
Γ ⊢ C[A2]
Γ, A1 ↔ A2 ⊢ C[A1]

Γ, B[A2] ⊢ C
Γ, A1 ↔ A2, B[A1] ⊢ C
-/
section
-- Tactic mode
example (Γ : Prop) (h : A1 ↔ A2) (hb : A1 ∨ B) : C := by
  rw [h] at hb
  -- Proof of Γ, A2 ∨ B ⊢ C
  sorry

end


end Logic
end
