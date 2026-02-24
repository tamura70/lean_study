/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Init.Data.Rat.Basic
import Mathlib.Tactic

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

lemma seq_comp2_apply (x : ℝ) (fs1 fs2 : List UnaryFunc) :
  ((seq fs1) ∘ (seq fs2)) x = (seq fs1) ((seq fs2) x) := by
  norm_num

lemma seq_comp3_apply (x : ℝ) (fs1 fs2 fs3 : List UnaryFunc) :
  (((seq fs1) ∘ (seq fs2)) ∘ (seq fs3)) x = (seq fs1) ((seq fs2) ((seq fs3) x)) := by
  norm_num

abbrev list_add_one := [squ, inv, cos, atan, sqrt]

abbrev list_add_n : Nat → List UnaryFunc
  | 0 => []
  | n + 1 => list_add_one ++ (list_add_n n)

abbrev list_neg := [log, inv, pow]

abbrev gen_int (i : Int) : List UnaryFunc :=
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

/--
UnaryFunc の合成で 0 から任意の整数を生成できる．
すなわち，任意の整数 i について seq (gen_int i) 0 = i
-/
theorem seq_gen_int (i : Int) :
  seq (gen_int i) 0 = i := by
  have : i < 0 ∨ i ≥ 0 := by exact Int.lt_or_le i 0
  obtain hn | hp := this
  case _ =>
    have : gen_int i = list_neg ++ list_add_n (- i).toNat := by
      exact if_pos hn
    rw [this]
    rw [seq_append_eq_seq_comp]
    rw [seq_comp2_apply]
    have hx : (0 : Real) ≥ 0 := by norm_num
    rw [seq_add_n hx, seq_neg]
    simp only [zero_add]
    norm_cast
    grind
  case _ =>
    have : gen_int i = list_add_n i.toNat := by
      simp [*]
    rw [this]
    have hx : (0 : Real) ≥ 0 := by norm_num
    rw [seq_add_n hx]
    norm_cast
    simp [*]

abbrev CFrac := List Nat

abbrev RatToCFrac' (num : Nat) (den : Nat) (hd : den > 0) : CFrac :=
  if h : num % den = 0 then
    [num / den]
  else
    have h1 : num % den > 0 := by grind
    (num / den) :: (RatToCFrac' den (num % den) h1)
  termination_by den
  decreasing_by exact Nat.mod_lt num hd

abbrev RatToCFrac (r : Rat) : CFrac :=
  have : r.den > 0 := by finiteness
  RatToCFrac' r.num.toNat r.den this

abbrev CFracToRat (c : CFrac) : Rat :=
  match c with
  | [] => 0
  | a :: c => a + 1 / (CFracToRat c)

#eval RatToCFrac' 355 113 (Nat.zero_lt_succ 112)
#eval CFracToRat [3, 7, 16]

#eval mkRat 2 4
#eval (2 : Rat) / (4 : Rat)

abbrev gen_cfrac (c : CFrac) : List UnaryFunc :=
  match c with
  | [] => []
  | a :: c => (list_add_n a) ++ [inv] ++ gen_cfrac c

abbrev gen_rat (r : Rat) : List UnaryFunc :=
  if r ≥ 0 then
    gen_cfrac (RatToCFrac r)
  else
    list_neg ++ gen_cfrac (RatToCFrac r.neg)

lemma cfractorat_ge_zero (c : CFrac) :
  CFracToRat c ≥ 0:= by
  induction c with
  | nil =>
    norm_num
  | cons a c ih =>
    unfold CFracToRat
    finiteness

lemma cfractorat (r : Rat) (hr : r ≥ 0) (c : CFrac) (h : RatToCFrac r = a :: c) :
  CFracToRat c = 1 / (r - a) := by
  have num_ge_zero : r.num ≥ 0 := by positivity
  have num_nat : r.num = r.num.toNat := by
    simp_all only [ge_iff_le, Rat.num_nonneg, Int.ofNat_toNat, sup_of_le_left]
  unfold RatToCFrac RatToCFrac' at h
  simp only at h
  split at h
  case isTrue ht =>
    simp only [List.cons.injEq, List.nil_eq] at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [h2]
    simp only [one_div, zero_eq_inv]
    zify at *
    -- field_simp at *
    sorry
  case isFalse hf =>
    simp only [one_div]
    zify at *
    sorry

theorem cfractorat_of_rattocfrac (c : CFrac) :
  ∀ r : Rat, r ≥ 0 → RatToCFrac r = c → CFracToRat c = r := by
  induction c with
  | nil =>
    unfold RatToCFrac CFracToRat
    intro r hr
    have : RatToCFrac r = [] → r = 0 := by
      unfold RatToCFrac RatToCFrac'
      grind
    tauto
  | cons a c ih =>
    intro r hr1 hr2
    have h : CFracToRat c = 1 / (r - a) := by
      apply cfractorat r hr1 c hr2
    unfold CFracToRat
    rw [h]
    norm_num

lemma seq_gen_cfrac (c : CFrac) :
  seq (gen_cfrac c) 0 = CFracToRat c := by
  induction c with
  | nil =>
    aesop
  | cons a c ih =>
    unfold gen_cfrac CFracToRat
    repeat rw [seq_append_eq_seq_comp]
    rw [seq_comp3_apply 0]
    rw [ih]
    have : seq [inv] (CFracToRat c) ≥ 0 := by
      unfold seq eval invx
      norm_num
      exact cfractorat_ge_zero c
    rw [seq_add_n this]
    unfold seq eval invx
    norm_num
    norm_cast
    grind

/--
UnaryFunc の合成で 0 から任意の非負の有理数を生成できる．
すなわち，任意の非負の有理数 r について seq (gen_rat r) 0 = r
-/
theorem seq_gen_rat (r : Rat) :
  seq (gen_rat r) 0 = r := by
  unfold gen_rat
  split
  case _ =>
    grind only [seq_gen_cfrac, Rat.cast_inj, cfractorat_of_rattocfrac]
  case _ =>
    have : - r ≥ 0 := by grind
    have hr : r.neg ≥ 0 := by finiteness
    have : seq (gen_cfrac (RatToCFrac r.neg)) 0 = r.neg := by
      grind only [seq_gen_cfrac, Rat.cast_inj, cfractorat_of_rattocfrac]
    repeat rw [seq_append_eq_seq_comp]
    rw [seq_comp2_apply]
    rw [this]
    rw [seq_neg]
    norm_cast
    exact neg_eq_iff_eq_neg.mpr rfl

end
