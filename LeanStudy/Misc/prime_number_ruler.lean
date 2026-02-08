/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
-- import Init.Data.Nat
-- import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
-- import Mathlib.Data.Set.Basic
-- import Mathlib.Algebra.Ring.Parity

/-!
# 素数モノサシ

完備な素数モノサシが有限個しか存在しないことの証明。

素数モノサシとは、両端を除く内部の目盛りが素数の位置にあるモノサシである。
完備な素数モノサシは、両端を含めた2つの目盛り間で、
1からモノサシの長さまですべての長さを測れるモノサシである。
ここでは、完備な素数モノサシの長さが122以下であることを証明する。

- https://tamura70.gitlab.io/papers/pdf/pnr.pdf
-/

/-!
素数
-/

section

/--
素数 p について p ≥ 3 のとき Odd p
-/
theorem prime_ge_3_is_odd (p : Nat) (hp : Nat.Prime p) (h3 : p ≥ 3) :
  p % 2 = 1 := by
  obtain hp_eq_2 | hp_odd := Nat.Prime.eq_two_or_odd' hp
  case _ => simp_all only [ge_iff_le, Nat.reduceLeDiff]
  case _ => exact Nat.odd_iff.mp hp_odd

/--
素数 p について p ≥ 5 のとき p % 6 = 1 or 5
-/
theorem prime_ge_5_is_1_or_5_mod_6 (p : Nat) (hp : Nat.Prime p) (h5 : p ≥ 5) :
  (p % 6 = 1) ∨ (p % 6 = 5) := by
  have hp_odd : p % 2 = 1 := by
    apply prime_ge_3_is_odd p hp
    exact Nat.le_of_add_left_le h5
  have h_a : (p % 6 = 1 ↔ p % 2 = 1 ∧ p % 3 = 1) := by omega
  have h_b : (p % 6 = 5 ↔ p % 2 = 1 ∧ p % 3 = 2) := by omega
  have h_c : (p % 3 ≠ 0 → p % 3 = 1 ∨ p % 3 = 2) := by omega
  rw [h_a, h_b, hp_odd]
  simp only [true_and]
  apply h_c
  show p % 3 ≠ 0
  by_contra hp_ne_0_mod_3
  have hp_eq_3 : p = 3 := by
    rw [← Nat.Prime.dvd_iff_eq hp]
    · exact Nat.dvd_of_mod_eq_zero hp_ne_0_mod_3
    · trivial
  simp_all only [ge_iff_le, Nat.reduceLeDiff]

end

/-!
素数モノサシ
-/

section
/--
SparseRuler の定義。目盛りの位置は任意。
-/
@[ext]
structure SparseRuler where
  len : Nat
  marks : Set Nat
  marksInside : ∀ m : Nat, m ∈ marks → (0 < m ∧ m < len)

/--
SparseRuler で m1 から m2 の目盛り間で長さ d を測れる条件
-/
def measure_d (ruler : SparseRuler) (d m1 m2 : Nat) : Prop :=
  (m1 ∈ ruler.marks ∨ m1 = 0 ∨ m1 = ruler.len)
  ∧ (m2 ∈ ruler.marks ∨ m2 = 0 ∨ m2 = ruler.len)
  ∧ m1 + d = m2

/--
SparseRuler で長さ d を測れる条件
-/
def canMeasure (ruler : SparseRuler) (d : Nat) : Prop :=
  ∃ (m1 m2 : Nat),
  measure_d ruler d m1 m2

/--
SparseRuler が完備である条件
-/
def CompleteRuler (ruler : SparseRuler) : Prop :=
  ∀ d : Nat, (0 < d ∧ d < ruler.len) → (canMeasure ruler d)

/--
SparseRuler が素数モノサシである条件
-/
def PrimeNumberRuler (ruler : SparseRuler) : Prop :=
  ∀ m ∈ ruler.marks, Nat.Prime m

/--
SparseRuler が完備素数モノサシである条件
-/
def CompletePrimeNumberRuler (ruler : SparseRuler) : Prop :=
  (PrimeNumberRuler ruler) ∧ (CompleteRuler ruler)

/--
SparseRuler で目盛り m1 から m2 で長さ d が測れるときに成り立つ範囲を示す
-/
lemma marks_bound (ruler : SparseRuler) (d m1 m2 : Nat) (hd : measure_d ruler d m1 m2) :
  (0 ≤ m1 ∧ m1 + d = m2 ∧ m2 ≤ ruler.len) := by
  obtain ⟨ hm1, hm2, hm ⟩ := hd
  have hm1_in := ruler.marksInside m1
  have hm2_in := ruler.marksInside m2
  and_intros
  · simp_all only [Nat.zero_le]
  · gcongr
  · obtain hm21 | hm22 | hm23 := hm2
    case _ =>
      have := hm2_in hm21
      omega
    case _ =>
      omega
    case _ =>
      simp_all only [lt_self_iff_false, and_false, imp_false, le_refl]

/--
長さ len ≥ 6 の完備素数モノサシは len = 素数 + 1 である
-/
lemma len_cpr_is_prime_plus_one
  (ruler : SparseRuler) (hr : ruler.len ≥ 6) (hcpr : CompletePrimeNumberRuler ruler) :
  (∃ p : Nat, Nat.Prime p ∧ ruler.len = p + 1) := by
  have primes := hcpr.left
  have complete := hcpr.right
  use ruler.len - 1
  rw [And.comm]
  constructor
  · omega
  show Nat.Prime (ruler.len - 1)
  let d := ruler.len - 1
  have measure_len_sub_1 : (canMeasure ruler d) := by
    apply complete
    constructor
    · omega
    · omega
  have mark_at_len_sub_1 : (d ∈ ruler.marks) := by
    rcases measure_len_sub_1 with ⟨m1, m2, hm⟩
    have bounds := marks_bound ruler d m1 m2 hm
    rcases hm with ⟨h1, h2, hm⟩
    have m2_ne_len : (m2 ≠ ruler.len) := by
      by_contra m2_eq_len
      have : m1 = 1 := by omega
      unfold PrimeNumberRuler at primes
      have : Nat.Prime 1 := by grind
      contradiction
    have : (m2 = d) := by omega
    rw [this] at bounds h2
    simp_all only [ge_iff_le, Nat.zero_le, true_and, Nat.add_eq_right, ne_eq, true_or, or_true,
      or_false]
    have : (d > 0) := by omega
    grind
  exact primes (ruler.len - 1) mark_at_len_sub_1

/--
長さ len ≥ 6 の完備素数モノサシは len % 6 = 0 or 2 である
-/
lemma len_cpr_is_0_or_2_mod_6
  (ruler : SparseRuler) (hr : ruler.len ≥ 6) (hcpr : CompletePrimeNumberRuler ruler) :
  (ruler.len % 6 = 0 ∨ ruler.len % 6 = 2) := by
  have a := prime_ge_5_is_1_or_5_mod_6 (ruler.len - 1)
  have b := len_cpr_is_prime_plus_one ruler hr hcpr
  rcases b with ⟨ p, hp ⟩
  rw [hp.right] at a hr
  have := a hp.left
  omega

/--
長さ len ≥ 6 の完備素数モノサシは Even len である
-/
lemma len_cpr_is_even
  (ruler : SparseRuler) (hr : ruler.len ≥ 6) (hcpr : CompletePrimeNumberRuler ruler) :
  (Even ruler.len) := by
  rw [Nat.even_iff]
  have := len_cpr_is_0_or_2_mod_6 ruler hr hcpr
  rcases this with h0 | h2
  case _ =>
    omega
  case _ =>
    omega

/--
長さ len ≥ 6 の完備素数モノサシで、奇数長さ d を測れるなら
Prime d ∨ Prime (d + 2) ∨ Prime (len - d) である
-/
lemma cpr_measure_odd
  (ruler : SparseRuler) (hr : ruler.len ≥ 6) (hcpr : CompletePrimeNumberRuler ruler)
  (d : Nat) (hd : d > 0 ∧ Odd d ∧ (canMeasure ruler d)) :
  (Nat.Prime d ∨ Nat.Prime (d + 2) ∨ Nat.Prime (ruler.len - d)) := by
  rcases hd with ⟨ hd_pos, hd_odd, hd_m ⟩
  rcases hd_m with ⟨ m1, m2, hm ⟩
  have bounds := marks_bound ruler d m1 m2 hm
  have len_even : (Even ruler.len) := len_cpr_is_even ruler hr hcpr
  have oe : (Odd m2 ↔ Even m1) := by
    have : m1 ≤ m2 := by omega
    rw [← Nat.odd_sub this]
    aesop
  rcases hm with ⟨ hm1, hm2, hm ⟩
  rcases hm1 with hm11 | hm12 | hm13
  case _ => -- m1 ∈ ruler.marks
    have m1p : Nat.Prime m1 := hcpr.left m1 hm11
    rcases hm2 with hm21 | hm22 | hm23
    case _ => -- m2 ∈ ruler.marks
      have m2p : Nat.Prime m2 := hcpr.left m2 hm21
      have m1_eq_2 : m1 = 2 := by
        rcases Nat.Prime.eq_two_or_odd' m1p with hm1_eq_2 | hm1_odd
        case _ =>
          gcongr
        case _ =>
          have : Odd m2 := by
            have : m1 ≥ 2 := by exact Nat.Prime.two_le m1p
            have : m2 ≥ 3 := by omega
            have : m2 % 2 = 1 := prime_ge_3_is_odd m2 m2p this
            exact Nat.odd_iff.mpr this
          rw [oe] at this
          rw [← Nat.not_odd_iff_even] at this
          contradiction
      rw [m1_eq_2] at hm
      apply Or.inr
      apply Or.inl
      have : m2 = d + 2 := by omega
      rw [← this]
      exact m2p
    case _ => -- m2 = 0
      simp_all only [ge_iff_le, gt_iff_lt, Nat.zero_le, and_self, Nat.not_odd_zero, false_iff,
        Nat.not_even_iff_odd, Nat.add_eq_zero_iff, zero_add, Nat.sub_zero, true_or]
    case _ => -- m2 = ruler.len
      apply Or.inr
      apply Or.inr
      show Nat.Prime (ruler.len - d)
      have : (ruler.len - d = m1) := by omega
      rw [this]
      exact m1p
  case _ => -- m1 = 0
    rw [hm12] at hm oe
    simp_all only [ge_iff_le, gt_iff_lt, le_refl, true_and, Even.zero, iff_true, zero_add]
    have m2p : (Nat.Prime m2) := by
      rcases hm2 with hm21 | hm22 | hm23
      case _ =>
        exact hcpr.left m2 hm21
      case _ =>
        simp_all only [lt_self_iff_false]
      case _ =>
        rw [← hm23, ← Nat.not_odd_iff_even] at len_even
        contradiction
    apply Or.inl
    show Nat.Prime m2
    rw [← hm]
    simp_all only
  case _ => -- m1 = ruler.len
    rw [hm13] at hm
    have hm2 : (m2 ∈ ruler.marks) := by omega
    have := by apply ruler.marksInside m2 hm2
    omega

/--
長さ len ≥ 6 の完備素数モノサシは len ≤ 122
-/
theorem cpr_len_limit
  (ruler : SparseRuler) (hr : ruler.len ≥ 6) (hcpr : CompletePrimeNumberRuler ruler)
  : (ruler.len ≤ 122) := by
  by_contra
  have hlen : ruler.len ≥ 123 := by omega
  rcases (len_cpr_is_0_or_2_mod_6 ruler hr hcpr) with hlen0 | hlen2
  case _ => -- ruler.len % 6 = 0
    let d := 33
    have : (canMeasure ruler d) := by
      apply hcpr.right d
      omega
    have hd : (d > 0 ∧ Odd d ∧ canMeasure ruler d) := by trivial
    have := cpr_measure_odd ruler hr hcpr d hd
    rcases this with hd1 | hd2 | hd3
    case _ =>
      have : ¬ Nat.Prime d := by decide
      contradiction
    case _ =>
      have : ¬ Nat.Prime (d + 2) := by decide
      contradiction
    case _ =>
      let p := ruler.len - d
      have : p ≥ 5 := by omega
      have := prime_ge_5_is_1_or_5_mod_6 p hd3 this
      have : ¬ Nat.Prime (p) := by omega
      contradiction
  case _ => -- ruler.len % 6 = 2
    let d := 119
    have : (canMeasure ruler d) := by
      apply hcpr.right d
      omega
    have hd : (d > 0 ∧ Odd d ∧ canMeasure ruler d) := by
      trivial
    have := cpr_measure_odd ruler hr hcpr d hd
    rcases this with hd1 | hd2 | hd3
    case _ =>
      have : ¬ Nat.Prime d := by decide
      contradiction
    case _ =>
      have : ¬ Nat.Prime (d + 2) := by decide
      contradiction
    case _ =>
      let p := ruler.len - d
      have : p ≥ 5 := by omega
      have := prime_ge_5_is_1_or_5_mod_6 p hd3 this
      have : ¬ Nat.Prime (p) := by omega
      contradiction

end
