/- 
{
  "name": "numpy.fix",
  "description": "Round to nearest integer towards zero",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fix.html",
  "doc": "Round to nearest integer towards zero.\n\nRounds an array of floats element-wise to nearest integer towards zero.",
}
-/

/-  numpy.fix: Round to nearest integer towards zero, element-wise.
    
    The fix (truncation) of each element x is the integer part of x,
    obtained by discarding the fractional part. This is equivalent to
    rounding towards zero.
    
    For positive numbers: fix(x) = floor(x)
    For negative numbers: fix(x) = ceil(x)
    
    Returns an array of the same shape as x, containing the fix of each element.
-/

/-  Specification: numpy.fix returns a vector where each element is the
    fix (truncation towards zero) of the corresponding element in x.
    
    Precondition: True (fix is defined for all real numbers)
    Postcondition: For all indices i, result[i] is the fix of x[i], meaning:
    - result[i] is an integer value (represented as Float)
    - |result[i]| ≤ |x[i]| (magnitude is reduced or equal)
    - result[i] has the same sign as x[i] (or zero if x[i] is zero)
    - |x[i] - result[i]| < 1 (difference is less than 1)
    - For positive x[i]: result[i] = floor(x[i])
    - For negative x[i]: result[i] = ceil(x[i])
    - For zero x[i]: result[i] = 0
    - Monotonicity: if x[i] ≤ x[j] then result[i] ≤ result[j]
    - Truncation property: result[i] truncates towards zero
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_fix {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem numpy_fix_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_fix x
    ⦃⇓result => ⌜∀ i : Fin n,
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      (result.get i).abs ≤ (x.get i).abs ∧
      (x.get i ≥ 0 → result.get i ≥ 0) ∧
      (x.get i ≤ 0 → result.get i ≤ 0) ∧
      (x.get i - result.get i).abs < 1 ∧
      (x.get i ≥ 0 → result.get i = (x.get i).floor) ∧
      (x.get i < 0 → result.get i = (x.get i).ceil) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
