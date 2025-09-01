/- 
{
  "name": "numpy.stack",
  "category": "Joining Arrays",
  "description": "Join a sequence of arrays along a new axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.stack.html",
  "doc": "Join a sequence of arrays along a new axis.\n\nThe \`axis\` parameter specifies the index of the new axis in the\ndimensions of the result. For example, if \`axis=0\` it will be the first\ndimension and if \`axis=-1\` it will be the last dimension.\n\nParameters\n----------\narrays : sequence of array_like\n    Each array must have the same shape.\naxis : int, optional\n    The axis in the result array along which the input arrays are stacked.\nout : ndarray, optional\n    If provided, the destination to place the result. The shape must be\n    correct, matching that of what stack would have returned if no\n    out argument were specified.\ndtype : str or dtype\n    If provided, the destination array will have this dtype. Cannot be\n    provided together with \`out\`.\ncasting : {'no', 'equiv', 'safe', 'same_kind', 'unsafe'}, optional\n    Controls what kind of data casting may occur. Defaults to 'same_kind'.\n\nReturns\n-------\nstacked : ndarray\n    The stacked array has one more dimension than the input arrays.\n\nExamples\n--------\n>>> arrays = [np.random.randn(3, 4) for _ in range(10)]\n>>> np.stack(arrays, axis=0).shape\n(10, 3, 4)\n>>> np.stack(arrays, axis=1).shape\n(3, 10, 4)\n>>> np.stack(arrays, axis=2).shape\n(3, 4, 10)",
  "signature": "numpy.stack(arrays, axis=0, out=None, *, dtype=None, casting='same_kind')",
  "source_location": "numpy/_core/shape_base.py"
}
-/

/-  Stack a sequence of vectors along a new axis to create a 2D matrix.
    For simplicity, we focus on stacking 1D vectors along axis 0.
    The result has shape (m, n) where m is the number of vectors and n is their common length. -/

/-  Specification: stack creates a 2D matrix where each input vector becomes a row.
    Key properties:
    1. The result preserves all input vectors as rows
    2. The i-th row of the result equals the i-th input vector
    3. Shape property: stacking m vectors of length n produces an m×n matrix -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def stack {m n : Nat} (arrays : Vector (Vector Float n) m) : Id (Vector (Vector Float n) m) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem stack_spec {m n : Nat} (arrays : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    stack arrays
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n, 
                  (result.get i).get j = (arrays.get i).get j⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
