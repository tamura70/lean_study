/-
Copyright (c) 2026 Naoyuki Tamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoyuki Tamura
-/
import LeanStudy.CSP.Basic
import LeanStudy.SAT.DirectEncoderCSP

section

open CSP
open SAT
open DirectEncoder

namespace DirectEncoder.Example

def iX : IVar := { name := "x", lb := 1, ub := 3 }
def iY : IVar := { name := "y", lb := 1, ub := 3 }

def csp : CSP := {
  ivariables := [iX, iY]
  constraints := [Constraint.ne iX iY]
  wf := by norm_num
}

#eval encode csp

example :
  ∀ val : CSP.Valuation,
  CSP.Sat val csp ↔ CNF.Sat (val_to_a val) (encode csp) := by
  exact fun val ↦ Iff.symm (sat_csp_iff_sat_cnf val csp)

end DirectEncoder.Example
end
