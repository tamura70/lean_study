/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import Mathlib
import Mathlib.Data.List.Intervals

namespace Util

abbrev IntRange (lb : Int) (ub : Int) : List Int :=
  let c : Nat := Int.toNat (ub - lb + 1)
  (List.range c).map (fun k => Int.ofNat k + lb)

#eval IntRange (-1 : Int) (5 : Int)

theorem intrange_iff_within (lb : Int) (ub : Int) (i : Int) :
  i ∈ IntRange lb ub ↔ lb ≤ i ∧ i ≤ ub := by
  constructor
  · unfold IntRange
    intro hi
    simp_all
    omega
  · intros hi
    unfold IntRange
    norm_num
    use (i - lb).toNat
    simp_all

end Util
