/- 
{
  "name": "nargs",
  "description": "The number of arguments the ufunc accepts",
  "details": "Equal to nin + nout"
}
-/

/-  numpy.ufunc.nargs: Returns the total number of arguments the ufunc accepts.

    This attribute represents the sum of input and output arguments for a ufunc.
    For example, np.add has nin=2, nout=1, so nargs=3.

    This is a read-only attribute that provides metadata about the ufunc's signature.
-/

/-  Specification: numpy.ufunc.nargs returns nin + nout

    Precondition: True (no special preconditions for reading metadata)
    Postcondition: The result equals the sum of input and output arguments
-/

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

-- <vc-helpers>
-- </vc-helpers>

def numpy_nargs (ufunc : Ufunc) : Id Nat :=
  sorry

theorem numpy_nargs_spec (ufunc : Ufunc) :
    ⦃⌜True⌝⦄
    numpy_nargs ufunc
    ⦃⇓result => ⌜result = ufunc.nin + ufunc.nout⌝⦄ := by
  sorry
