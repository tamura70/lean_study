/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.Real.Basic
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

noncomputable abbrev pi_div_180 := Real.pi / 180
noncomputable abbrev rad : ℝ → ℝ := fun x ↦ (pi_div_180 * x)
noncomputable abbrev deg : ℝ → ℝ := fun x ↦ (x / pi_div_180)
noncomputable abbrev sinx : ℝ → ℝ := fun x ↦ Real.sin (rad x)
noncomputable abbrev cosx : ℝ → ℝ := fun x ↦ Real.cos (rad x)
noncomputable abbrev tanx : ℝ → ℝ := fun x ↦ Real.tan (rad x)
noncomputable abbrev asinx : ℝ → ℝ := fun x ↦ deg (Real.arcsin x)
noncomputable abbrev acosx : ℝ → ℝ := fun x ↦ deg (Real.arccos x)
noncomputable abbrev atanx : ℝ → ℝ := fun x ↦ deg (Real.arctan x)
noncomputable abbrev invx : ℝ → ℝ := fun x ↦ x⁻¹
noncomputable abbrev squx : ℝ → ℝ := fun x ↦ x ^ 2
noncomputable abbrev sqrtx : ℝ → ℝ := fun x ↦ Real.sqrt x
noncomputable abbrev powx : ℝ → ℝ := fun x ↦ 10 ^ x
noncomputable abbrev logx : ℝ → ℝ := fun x ↦ Real.logb 10 x

inductive UnaryFunc where
| sin
| cos
| tan
| asin
| acos
| atan
| inv
| squ
| sqrt
| pow
| log
deriving Repr

open UnaryFunc

noncomputable abbrev eval (f : UnaryFunc) : ℝ → ℝ :=
  match f with
  | sin => sinx
  | cos => cosx
  | tan => tanx
  | asin => asinx
  | acos => acosx
  | atan => atanx
  | inv => invx
  | squ => squx
  | sqrt => sqrtx
  | pow => powx
  | log => logx

lemma deg_rad (d : ℝ) : deg (rad d) = d := by
  unfold deg rad
  field_simp

lemma rad_deg (x : ℝ) : rad (deg x) = x := by
  unfold deg rad
  field_simp

lemma log_pow (x : ℝ) : logx (powx x) = x := by
  norm_num

lemma add_one_x (hx : x ≥ 0) :
  (squx (invx (cosx (atanx (sqrtx x))))) = x + 1 := by
  unfold squx invx cosx atanx sqrtx
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

lemma neg_x :
  (logx (invx (powx x))) = - x := by
  unfold logx invx powx
  rw [Real.logb_inv]
  rw [Real.logb_rpow]
  · positivity
  · norm_num

noncomputable abbrev seq (fs: List UnaryFunc) : (ℝ → ℝ) :=
  (fs.map eval).foldr (fun (f g) => f ∘ g) id

lemma seq_append_eq_seq_comp (fs gs : List UnaryFunc) :
  seq (fs ++ gs) = seq fs ∘ seq gs := by
  induction fs with
  | nil =>
    trivial
  | cons f fs ih =>
    have : (f :: fs) ++ gs = f :: (fs ++ gs) := by norm_num
    rw [this]
    have h1 : seq (f :: fs) = (eval f) ∘ (seq fs) := by trivial
    have h2 : seq (f :: (fs ++ gs)) = (eval f) ∘ (seq (fs ++ gs)) := by trivial
    rw [h1, h2]
    rw [ih]
    trivial

lemma seq_comp_apply (x : ℝ) (fs gs : List UnaryFunc) :
  ((seq fs) ∘ (seq gs)) x = (seq fs) ((seq gs) x) := by
  norm_num

abbrev list_add_one := [squ, inv, cos, atan, sqrt]

abbrev list_add_n : Nat → List UnaryFunc
  | 0 => []
  | n + 1 => list_add_one ++ (list_add_n n)

abbrev list_neg := [log, inv, pow]

abbrev gen_i (i : Int) : List UnaryFunc :=
  if i < 0 then
    list_neg ++ list_add_n (- i).toNat
  else
    list_add_n i.toNat

-- #eval gen_i (-2 : Int)

/--
x ≥ 0 のとき seq list_add_one x は x + 1 に等しい
-/
lemma seq_add_one (hx : x ≥ 0) :
  seq list_add_one x = x + 1 := by
  rw [← add_one_x hx]
  trivial

/--
x ≥ 0 のとき seq (list_add_n n) x は x + n に等しい
-/
lemma seq_add_n (hx : x ≥ 0) (n : Nat) :
  seq (list_add_n n) x = x + n := by
  induction n with
  | zero =>
    aesop
  | succ n' ih =>
    unfold list_add_n
    rw [seq_append_eq_seq_comp]
    let f := seq list_add_one
    set g := seq (list_add_n n')
    have : (f ∘ g) x = f (g x) := by norm_num
    rw [this, ih]
    have : f (x + ↑n') = x + ↑n' + 1 := by
      have : x + n' ≥ 0 := by finiteness
      grind only [seq_add_one]
    grind

/--
seq list_neg x は - x に等しい
-/
lemma seq_neg :
  seq list_neg x = - x := by
  rw [← neg_x]
  trivial

/-
任意の整数 i について seq (gen_i i) 0 = i
-/
theorem seq_gen_i (i : Int) :
  seq (gen_i i) 0 = i := by
  have : i < 0 ∨ i ≥ 0 := by exact Int.lt_or_le i 0
  obtain hn | hp := this
  case _ =>
    have : gen_i i = list_neg ++ list_add_n (- i).toNat := by
      exact if_pos hn
    rw [this]
    rw [seq_append_eq_seq_comp]
    rw [seq_comp_apply]
    have hx : (0 : Real) ≥ 0 := by norm_num
    rw [seq_add_n hx, seq_neg]
    simp only [zero_add]
    norm_cast
    grind
  case _ =>
    have : gen_i i = list_add_n i.toNat := by
      simp [*]
    rw [this]
    have hx : (0 : Real) ≥ 0 := by norm_num
    rw [seq_add_n hx]
    norm_cast
    simp [*]

/-
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/ContinuedFractions/Basic.html
-/


end
