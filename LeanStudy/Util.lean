import Mathlib.Tactic

section

namespace Util

def combinations2 : List α → List (α × α)
  | [] => []
  | x :: xs => (List.product [x] xs) ++ combinations2 xs

theorem comb2_pair (xs : List α) (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  (x, y) ∈ (combinations2 xs) ∨ (y, x) ∈ (combinations2 xs) := by
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih1 =>
    have : (x = x1 ∧ y ∈ xs1) ∨ (x ∈ xs1 ∧ y = x1) ∨ (x ∈ xs1 ∧ y ∈ xs1) := by
      grind
    obtain h1 | h2 | h3 := this
    case _ =>
      apply Or.inl
      unfold combinations2
      simp_all
    case _ =>
      apply Or.inr
      unfold combinations2
      simp_all
    case _ =>
      unfold combinations2
      obtain h4 | h5 := ih1 h3.left h3.right
      case _ =>
        simp_all
      case _ =>
        simp_all

theorem comb2_some_pair (xs : List α) (hxs : List.Nodup xs) (xy : α × α) :
  xy ∈ (combinations2 xs) → ∃ x, ∃ y, x ∈ xs ∧ y ∈ xs ∧ x ≠ y ∧ xy = (x, y) := by
  intro hxy
  unfold combinations2 at hxy
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih1 =>
    have : xy ∈ [x1].product xs1 ∨ xy ∈ combinations2 xs1 := by
      aesop
    use xy.1
    use xy.2
    obtain hxy1 | hxy2 := this
    case _ =>
      aesop
    case _ =>
      grind [= combinations2]

end Util
end
