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

theorem comb2_pair (xs : List α) (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x ≠ y) :
  -- ∀ xys, xys = combinations2 xs → (x, y) ∈ xys ∨ (y, x) ∈ xys := by
  (x, y) ∈ combinations2 xs ∨ (y, x) ∈ combinations2 xs := by
  induction xs with
  | nil =>
    trivial
  | cons x1 xs1 ih =>
    sorry

end Util
end
