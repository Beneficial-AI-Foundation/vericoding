import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.asmatrix",
  "category": "From existing data",
  "description": "Interpret the input as a matrix",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.asmatrix.html",
  "doc": "\nInterpret the input as a matrix.\n\nParameters\n----------\ndata : array_like\n    Input data.\ndtype : data-type\n    Data-type of the output matrix.\n\nReturns\n-------\nmat : matrix\n    data interpreted as a matrix.\n\nExamples\n--------\n>>> x = np.array([[1, 2], [3, 4]])\n\n>>> m = np.asmatrix(x)\n\n>>> x[0,0] = 5\n\n>>> m\nmatrix([[5, 2],\n        [3, 4]])\n\nNotes\n-----\nUnlike matrix, asmatrix does not make a copy if the input is already a matrix or an ndarray. \nEquivalent to matrix(data, copy=False).\n",
  "code": "def asmatrix(data, dtype=None):\n    \"\"\"\n    Interpret the input as a matrix.\n\n    Unlike `matrix`, `asmatrix` does not make a copy if the input is already\n    a matrix or an ndarray.  Equivalent to ``matrix(data, copy=False)``.\n    \"\"\"\n    return matrix(data, dtype=dtype, copy=False)",
  "signature": "numpy.asmatrix(data, dtype=None)"
}
-/

open Std.Do

/-- Interpret the input as a matrix. In our simplified model, this represents
    a 1D vector as a matrix type. Since numpy.asmatrix doesn't make a copy
    if the input is already a matrix or ndarray, this function acts as an
    identity operation with matrix type semantics. -/
def asmatrix {n : Nat} (data : Vector Float n) : Id (Vector Float n) :=
  pure data

/-- Specification: asmatrix interprets input data as a matrix without copying.
    
    The function preserves the original data structure and values while
    providing matrix semantics. For our Vector-based implementation, this
    means the output vector has the same length and contains the same elements
    as the input vector.
    
    Key properties:
    1. No copying occurs - the result has the same elements as input
    2. The length is preserved  
    3. Element order is preserved
    4. All original values are maintained -/
theorem asmatrix_spec {n : Nat} (data : Vector Float n) :
    ⦃⌜True⌝⦄
    asmatrix data
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = data.get i⌝⦄ := by
  apply Std.Do.triple_pure
  simp