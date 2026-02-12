/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Under Construction

0 から始めて、単項関数 sin, cos, tan, asin, atan, inv, squ, sqrt, pow, log を
順に適用することで、任意の整数および任意の有理数を生成できることを示す。

- https://tamura70.gitlab.io/web-puzzle/calc/
-/
section

noncomputable def rad : ℝ → ℝ := fun x ↦ ((Real.pi / 180) * x)
noncomputable def deg : ℝ → ℝ := fun x ↦ ((Real.pi / 180)⁻¹ * x)
noncomputable def sin : ℝ → ℝ := fun x ↦ Real.sin (rad x)
noncomputable def cos : ℝ → ℝ := fun x ↦ Real.cos (rad x)
noncomputable def tan : ℝ → ℝ := fun x ↦ Real.tan (rad x)
noncomputable def asin : ℝ → ℝ := fun x ↦ deg (Real.arcsin x)
noncomputable def acos : ℝ → ℝ := fun x ↦ deg (Real.arccos x)
noncomputable def atan : ℝ → ℝ := fun x ↦ deg (Real.arctan x)
noncomputable def inv : ℝ → ℝ := fun x ↦ x⁻¹
noncomputable def squ : ℝ → ℝ := fun x ↦ x ^ 2
noncomputable def sqrt : ℝ → ℝ := fun x ↦ Real.sqrt x
noncomputable def pow : ℝ → ℝ := fun x ↦ 10 ^ x
noncomputable def log : ℝ → ℝ := fun x ↦ Real.logb 10 x

noncomputable def seq : List (ℝ → ℝ) → (ℝ → ℝ)
| [] => fun x ↦ x
| [f] => f
| f::fs => (seq fs) ∘ f

lemma log_pow (x : Real) : log (pow x) = x := by
  unfold log pow
  norm_num

lemma deg_rad (d : Real) : deg (rad d) = d := by
  unfold deg rad
  field_simp

lemma rad_deg (x : Real) : rad (deg x) = x := by
  unfold deg rad
  field_simp

lemma add_one_x {x : Real} (hx : x ≥ 0)
  : (squ (inv (cos (atan (sqrt x))))) = x + 1 := by
  unfold squ inv sqrt cos atan
  have : √ x ≥ 0 := by bound
  rw [Real.arctan_eq_arccos this]
  rw [rad_deg]
  rw [Real.cos_arccos]
  · rw [inv_inv]
    rw [Real.sq_sqrt hx]
    rw [Real.sq_sqrt]
    · ring
    · positivity
  · rw [Real.sq_sqrt hx]
    have : (√(1 + x))⁻¹ ≥ 0 := by positivity
    grind
  · bound

/--
x ≥ 0 のとき (squ ∘ inv ∘ cos ∘ atan ∘ sqrt) x は x + 1 に等しい
-/
lemma add_one {x : Real} (hx : x ≥ 0)
  : (squ ∘ inv ∘ cos ∘ atan ∘ sqrt) x = x + 1 := by
  have : (squ ∘ inv ∘ cos ∘ atan ∘ sqrt) x = (squ (inv (cos (atan (sqrt x))))) := by
    norm_num
  rw [this]
  exact add_one_x hx

lemma neg_x {x : Real}
  : (log (inv (pow x))) = - x := by
  unfold log inv pow
  rw [Real.logb_inv]
  rw [Real.logb_rpow]
  · positivity
  · norm_num

/--
(log ∘ inv ∘ pow) x は - x に等しい
-/
lemma neg {x : Real}
  : (log ∘ inv ∘ pow) x = - x := by
  have : (log ∘ inv ∘ pow) x = (log (inv (pow x))) := by
    norm_num
  rw [this]
  exact neg_x

example : seq [inv, inv] = id := by
  have : seq [inv, inv] = inv ∘ inv := by trivial
  rw [this]
  unfold inv
  norm_num

example : seq [pow, log] = id := by
  have : seq [pow, log] = log ∘ pow := by trivial
  rw [this]
  have : (∀ x, (log ∘ pow) x = id x) → (log ∘ pow) = id := by
    exact fun a ↦ Function.RightInverse.id a
  apply this
  intro x
  unfold log pow id
  simp_all only [Function.comp_apply, id_eq]
  norm_num

lemma seq_apply (f : ℝ → ℝ) (fs : List (ℝ → ℝ))
  : seq (f::fs) = (seq fs) ∘ f := by
  set x := (seq fs) ∘ f with hx
  unfold seq
  split
  · trivial
  · aesop
  · simp_all only [imp_false, List.cons.injEq]

lemma add_one_seq {x : Real} (hx : x ≥ 0) (fs : List (ℝ → ℝ))
  : seq (sqrt::atan::cos::inv::squ::fs) x = seq fs (x + 1) := by
  repeat rw [seq_apply]
  simp only [Function.comp_apply]
  rw [add_one_x hx]

lemma neg_seq {x : Real} (fs : List (ℝ → ℝ))
  : seq (pow::inv::log::fs) x = (seq fs) (- x) := by
  repeat rw [seq_apply]
  simp only [Function.comp_apply]
  rw [neg_x]

/-
noncomputable def prepend_add_n (n : Int) (fs : List (ℝ → ℝ)) : List (ℝ → ℝ) :=
  match n with
  | 0 => fs
  | n' + 1 => sqrt::atan::cos::inv::squ::(prepend_add_n n' fs)

theorem add_n_seq (hx : x ≥ 0) (n : Int) (fs : List (ℝ → ℝ))
  : seq (prepend_add_n n fs) x = seq fs (x + n) := by
  induction n with
  | zero =>
    aesop
  | succ n' h =>
    unfold prepend_add_n
    rw [add_one_seq hx]
    sorry
-/

/-
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/ContinuedFractions/Basic.html
-/


end
