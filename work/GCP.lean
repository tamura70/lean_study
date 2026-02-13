/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.CSP.Basic
import LeanStudy.SAT.DirectEncoderCSP

section

namespace GCP

structure Graph (V : Type) where
  vertices : List V
  adj : V → V → Bool
  symm : ∀ (u v : V), adj u v = adj v u
  loopless : ∀ v : V, adj v v = false

def edges (G : Graph V) : List (V × V) :=
  (Util.combinations2 G.vertices).filter (fun (u, v) => G.adj u v)

#check edges

def CompleteGraph (n : Nat) : Graph Nat where
  vertices := List.range n
  adj := fun u => fun v => u != v
  symm := by exact fun u v ↦ bne_comm
  loopless := by norm_num

def Coloring (G : Graph V) (coloring : V → C) :=
  ∀ e ∈ G.edges, coloring e.1 ≠ coloring e.2

def Colorable (G : Graph V) (c : Nat) :=
  ∃ coloring : V → Nat, Coloring G coloring ∧ ∀ v ∈ G.vertices, coloring v < c

end Graph

end
