/- 
{
  "name": "numpy.isfinite",
  "category": "Array contents testing",
  "description": "Test element-wise for finiteness (not infinity and not Not a Number)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.isfinite.html",
  "doc": "Test element-wise for finiteness (not infinity or not Not a Number).\n\nThe result is returned as a boolean array.\n\nParameters\n----------\nx : array_like\n    Input values.\nout : ndarray, None, or tuple of ndarray and None, optional\n    A location into which the result is stored. If provided, it must have\n    a shape that the inputs broadcast to. If not provided or None,\n    a freshly-allocated array is returned. A tuple (possible only as a\n    keyword argument) must have length equal to the number of outputs.\nwhere : array_like, optional\n    This condition is broadcast over the input. At locations where the\n    condition is True, the out array will be set to the ufunc result.\n    Elsewhere, the out array will retain its original value.\n    Note that if an uninitialized out array is created via the default\n    out=None, locations within it where the condition is False will\n    remain uninitialized.\n**kwargs\n    For other keyword-only arguments, see the\n    ufunc docs.\n\nReturns\n-------\ny : ndarray, bool\n    True where x is not positive infinity, negative infinity,\n    or NaN; false otherwise.\n    This is a scalar if x is a scalar.\n\nSee Also\n--------\nisinf, isneginf, isposinf, isnan\n\nNotes\n-----\nNot a Number, positive infinity and negative infinity are considered\nto be non-finite.\n\nNumPy uses the IEEE Standard for Binary Floating-Point for Arithmetic\n(IEEE 754). This means that Not a Number is not equivalent to infinity.\nAlso that positive infinity is not equivalent to negative infinity. But\ninfinity is equivalent to positive infinity.  Errors result if the\nsecond argument is also supplied when x is a scalar input, or if\nfirst and second arguments have different shapes.\n\nExamples\n--------\n>>> np.isfinite(1)\nTrue\n>>> np.isfinite(0)\nTrue\n>>> np.isfinite(np.nan)\nFalse\n>>> np.isfinite(np.inf)\nFalse\n>>> np.isfinite(np.NINF)\nFalse\n>>> np.isfinite([np.log(-1.),1.,np.log(0)])\narray([False,  True, False])\n\n>>> x = np.array([-np.inf, 0., np.inf])\n>>> y = np.array([2, 2, 2])\n>>> np.isfinite(x, y)\narray([0, 1, 0])\n>>> y\narray([0, 1, 0])",
}
-/

/-  Test element-wise for finiteness (not infinity and not NaN) -/

/-  Specification: isfinite returns true for finite values, false for infinity and NaN -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def isfinite {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry

theorem isfinite_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isfinite x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 
      (¬(x.get i).isInf ∧ ¬(x.get i).isNaN) ∧
      -- Core mathematical property: equivalence with isFinite
      (result.get i = true ↔ (x.get i).isFinite) ∧
      -- Inverse property: false iff NaN or infinity
      (result.get i = false ↔ ((x.get i).isNaN ∨ (x.get i).isInf)) ∧
      -- Specific cases: zero and normal numbers are finite
      (x.get i = 0.0 → result.get i = true) ∧
      -- Mathematical property: finite numbers have bounded absolute value
      (result.get i = true → ∃ (bound : Float), Float.abs (x.get i) ≤ bound) ∧
      -- Consistency: if not finite, then either NaN or infinity
      (result.get i = false → ((x.get i).isNaN ∨ (x.get i).isInf)) ∧
      -- Arithmetic stability: finite + finite arithmetic operations
      (result.get i = true → ∀ (y : Float), y.isFinite → 
        ((x.get i + y).isFinite ∨ (x.get i + y).isInf)) ∧
      -- IEEE 754 compliance: finite values exclude special values
      (result.get i = true → ¬(x.get i).isNaN ∧ ¬(x.get i).isInf)⌝⦄ := by
  sorry
