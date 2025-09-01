/- 
{
  "name": "numpy.fromfunction",
  "category": "From existing data",
  "description": "Construct an array by executing a function over each coordinate",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fromfunction.html",
  "doc": "\nConstruct an array by executing a function over each coordinate.\n\nParameters\n----------\nfunction : callable\n    The function is called with N parameters, where N is the rank of shape. Each parameter represents \n    the coordinates of the array varying along a specific axis.\nshape : (N,) tuple of ints\n    Shape of the output array, which also determines the shape of the coordinate arrays passed to function.\ndtype : data-type, optional\n    Data-type of the coordinate arrays passed to function. By default, dtype is float.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n**kwargs : keyword arguments, optional\n    Any keyword arguments to pass to function.\n\nReturns\n-------\nfromfunction : ndarray\n    The result of the call to function is passed back directly. Therefore the shape of fromfunction \n    is completely determined by function.\n\nExamples\n--------\n>>> np.fromfunction(lambda i, j: i == j, (3, 3), dtype=int)\narray([[ True, False, False],\n       [False,  True, False],\n       [False, False,  True]])\n\n>>> np.fromfunction(lambda i, j: i + j, (3, 3), dtype=int)\narray([[0, 1, 2],\n       [1, 2, 3],\n       [2, 3, 4]])\n",
  "signature": "numpy.fromfunction(function, shape, *, dtype=<class 'float'>, like=None, **kwargs)"
}
-/

/-  Construct a vector by executing a function over each coordinate index.
    For 1D case, this creates a vector of length n where element i is f(i). -/

/-  Specification: fromfunction creates a vector where each element is the result
    of applying the function to its index position. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def fromfunction {n : Nat} (f : Fin n → Float) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem fromfunction_spec {n : Nat} (f : Fin n → Float) :
    ⦃⌜True⌝⦄
    fromfunction f
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = f i⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
