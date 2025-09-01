/- 
{
  "name": "numpy.vstack",
  "category": "Joining Arrays",
  "description": "Stack arrays in sequence vertically (row wise)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.vstack.html",
  "doc": "Stack arrays in sequence vertically (row wise).\n\nThis is equivalent to concatenation along the first axis after 1-D arrays\nof shape \`(N,)\` have been reshaped to \`(1,N)\`. Rebuilds arrays divided by\n\`vsplit\`.\n\nThis function makes most sense for arrays with up to 3 dimensions. For\ninstance, for pixel-data with a height (first axis), width (second axis),\nand r/g/b channels (third axis). The functions \`concatenate\`, \`stack\` and\n\`block\` provide more general stacking and concatenation operations.\n\nParameters\n----------\ntup : sequence of ndarrays\n    The arrays must have the same shape along all but the first axis.\n    1-D arrays must have the same length.\ndtype : str or dtype\n    If provided, the destination array will have this dtype. Cannot be\n    provided together with \`out\`.\ncasting : {'no', 'equiv', 'safe', 'same_kind', 'unsafe'}, optional\n    Controls what kind of data casting may occur. Defaults to 'same_kind'.\n\nReturns\n-------\nstacked : ndarray\n    The array formed by stacking the given arrays, will be at least 2-D.\n\nExamples\n--------\n>>> a = np.array([1, 2, 3])\n>>> b = np.array([4, 5, 6])\n>>> np.vstack((a,b))\narray([[1, 2, 3],\n       [4, 5, 6]])\n>>> a = np.array([[1], [2], [3]])\n>>> b = np.array([[4], [5], [6]])\n>>> np.vstack((a,b))\narray([[1],\n       [2],\n       [3],\n       [4],\n       [5],\n       [6]])",
  "source_location": "numpy/_core/shape_base.py",
  "signature": "numpy.vstack(tup, *, dtype=None, casting='same_kind')"
}
-/

/-  Stack two vectors vertically to create a 2D matrix.
    For 1D vectors, this treats them as row vectors and stacks them vertically.
    This is a simplified version focusing on the common case of stacking two 1D vectors. -/

/-  Specification: vstack stacks two vectors vertically, creating a 2x n matrix
    where the first row is vector a and the second row is vector b.
    
    Mathematical properties:
    1. The result has shape (2, n) where n is the length of input vectors
    2. The first row of the result equals the first input vector
    3. The second row of the result equals the second input vector
    4. This operation preserves the elements and their order within each vector -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def vstack {n : Nat} (a b : Vector Float n) : Id (Vector (Vector Float n) 2) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem vstack_spec {n : Nat} (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    vstack a b
    ⦃⇓result => ⌜(∀ j : Fin n, (result.get 0).get j = a.get j) ∧
                 (∀ j : Fin n, (result.get 1).get j = b.get j)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
