/- 
{
  "name": "numpy.where",
  "category": "Boolean/mask indexing",
  "description": "Return elements chosen from x or y depending on condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.where.html",
  "doc": "Return elements chosen from \`x\` or \`y\` depending on \`condition\`.\n\nParameters\n----------\ncondition : array_like, bool\n    Where True, yield \`x\`, otherwise yield \`y\`.\nx, y : array_like\n    Values from which to choose. \`x\`, \`y\` and \`condition\` need to be broadcastable to some shape.\n\nReturns\n-------\nout : ndarray\n    If both \`x\` and \`y\` are given, the output array contains elements of \`x\` where \`condition\` is True, and those from \`y\` elsewhere.\n\nNote\n----\nIf only \`condition\` is given, return \`\`condition.nonzero()\`\`.",
}
-/

/-  Return elements chosen from x or y depending on condition.
    Given vectors of equal length for condition, x, and y, constructs a result vector
    where each element is selected from x if the corresponding condition is true,
    otherwise from y.

    This implements the core ternary conditional operation:
    result[i] = condition[i] ? x[i] : y[i]

    The function requires all three input vectors to have the same length, which
    is enforced by the type system using Vector types. -/

/-  Specification: where returns elements chosen from x or y based on condition.
    This captures the essential behavior of numpy.where function:

    Mathematical properties:
    1. The result has the same length as all input vectors
    2. For each position i, if condition[i] is true, then result[i] = x[i]
    3. For each position i, if condition[i] is false, then result[i] = y[i]
    4. The function is deterministic - same inputs always produce same output
    5. The result is well-defined for all inputs (no partial functions)

    This specification captures the core ternary conditional semantics:
    result[i] = if condition.get i then x.get i else y.get i

    The use of Vector types ensures type safety and eliminates the need for
    size compatibility checks at runtime. All vectors must have the same length
    by construction. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def «where» {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem where_spec {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    «where» condition x y
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = if condition.get i then x.get i else y.get i⌝⦄ := by
  sorry
