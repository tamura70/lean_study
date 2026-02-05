import Mathlib.Tactic

section

namespace Util

def combinations2 : List α → List (α × α)
  | [] => []
  | x :: xs =>
    let rec f : List α → List (α × α)
    | [] => []
    | x1 :: xs1 => (x, x1) :: (f xs1)
    (f xs) ++ combinations2 xs

lemma comb2_f (xs : List α) (x y : α) (hy : y ∈ xs) :
  (x, y) ∈ combinations2.f x xs := by
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih =>
    have : (y = x1) ∨ (y ∈ xs1) := by simp_all only [List.mem_cons]
    obtain hy1 | hy2 := this
    case _ =>
      grind [= combinations2.f]
    case _ =>
      exact List.mem_of_mem_tail (ih hy2)

theorem comb2_pair (xs : List α) (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  (x, y) ∈ combinations2 xs ∨ (y, x) ∈ combinations2 xs := by
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
      have : (x, y) ∈ combinations2.f x xs1 := comb2_f xs1 x y h1.right
      simp_all only [ne_eq, forall_const, List.mem_cons, true_or, or_true, List.mem_append]
    case _ =>
      apply Or.inr
      unfold combinations2
      have : (y, x) ∈ combinations2.f y xs1 := comb2_f xs1 y x h2.left
      simp_all only [ne_eq, forall_const, List.mem_cons, or_true, true_or, List.mem_append]
    case _ =>
      unfold combinations2 combinations2.f
      obtain h4 | h5 := ih1 h3.left h3.right
      case _ =>
        simp_all only [ne_eq, true_or, imp_self, List.mem_cons, or_true, List.mem_append]
      case _ =>
        simp_all only [ne_eq, or_true, imp_self, List.mem_cons, List.mem_append]

end Util
end
