import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import LeanStudy.SAT.Basic

section

def combinations2 : List α → List (α × α)
  | [] => []
  | x :: xs =>
    let rec f : List α → List (α × α)
    | [] => []
    | x1 :: xs1 => (x, x1) :: (f xs1)
    (f xs) ++ combinations2 xs

#eval combinations2 [1, 2, 3]

structure MyGraph (V : Type) where
  vertices : List V
  adj : V → V → Bool
  symm : ∀ (u v : V), adj u v = adj v u
  loopless : ∀ v : V, adj v v = false

def edges (G : MyGraph V) : List (V × V) :=
  (combinations2 G.vertices).filter (fun (u, v) => G.adj u v)

def MyCompleteGraph (n : Nat) : MyGraph Nat where
  vertices := List.range n
  adj := fun u => fun v => u != v
  symm := by exact fun u v ↦ bne_comm
  loopless := by norm_num

def toSimpleGraph (G : MyGraph V) : SimpleGraph V :=
  let Adj : V → V → Prop := (fun u => fun v => G.adj u v = true)
  have symm : Symmetric Adj := by
    unfold Symmetric Adj
    intros u v huv
    rw [← G.symm u v]
    assumption
  have loopless : Irreflexive Adj := by
    unfold Irreflexive Adj
    intro v
    norm_num
    exact G.loopless v
  SimpleGraph.mk Adj symm loopless

#check toSimpleGraph (MyCompleteGraph 3)




def at_least_one (xs : List (SAT.Literal V)) : SAT.CNF V :=
  [xs]

def at_most_one (xs : List (SAT.Literal V)) : SAT.CNF V :=
  (combinations2 xs).map (fun (x1, x2) => [x1.negate, x2.negate])

def exact_one (xs : List (SAT.Literal V)) : SAT.CNF V :=
  at_least_one xs ++ at_most_one xs

#eval at_least_one ([1, 2, 3].map (fun i => (i, true)))
#eval at_most_one ([1, 2, 3].map (fun i => (i, true)))

def coloring_direct_encoder (G : MyGraph V) (c : Nat) : SAT.CNF (V × Nat) :=
  let cnf1 : SAT.CNF (V × Nat) :=
    G.vertices.flatMap
    fun v =>
      let xs := (List.range c).map (fun k => ((v, k), true))
      exact_one xs
  let cnf2 :=
    (edges G).flatMap
    (fun (u, v) =>
      (List.range c).map
      (fun k => [((u, k), false), ((v, k), false)])
    )
  cnf1 ++ cnf2

#eval coloring_direct_encoder (MyCompleteGraph 3) 3

end
