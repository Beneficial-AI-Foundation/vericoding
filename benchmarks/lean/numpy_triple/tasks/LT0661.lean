-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
set_option linter.missingDocs false
open Std.Do

/-- Represents a universal function (ufunc) type that captures basic metadata about 
    the number of inputs and outputs. In NumPy, this would be the ufunc object itself. -/
structure UFunc where
  /-- Number of input arguments the ufunc accepts -/
  nin : Nat      
  /-- Number of output arguments the ufunc produces -/
  nout_val : Nat 
  /-- Proof that nout_val is always at least 1, since all ufuncs can take output arguments -/
  h_nout_pos : nout_val ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nout (ufunc : UFunc) : Id Nat :=
  pure ufunc.nout_val
-- </vc-definitions>

-- <vc-theorems>
theorem nout_spec (ufunc : UFunc) :
    ⦃⌜True⌝⦄
    nout ufunc
    ⦃⇓result => ⌜result = ufunc.nout_val ∧ result ≥ 1⌝⦄ := by
  sorry
-- </vc-theorems>