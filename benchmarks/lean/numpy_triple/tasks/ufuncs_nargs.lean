-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing a NumPy universal function (ufunc) with its metadata -/
structure Ufunc where
  /-- Number of input arguments the ufunc accepts -/
  nin : Nat
  /-- Number of output arguments the ufunc produces -/
  nout : Nat
  deriving Repr, DecidableEq
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_nargs (ufunc : Ufunc) : Id Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_nargs_spec (ufunc : Ufunc) :
    ⦃⌜True⌝⦄
    numpy_nargs ufunc
    ⦃⇓result => ⌜result = ufunc.nin + ufunc.nout⌝⦄ := by
  sorry
-- </vc-theorems>