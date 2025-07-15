import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.shape",
  "category": "Basic Operations",
  "description": "Return the shape of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.shape.html",
  "doc": "Return the shape of an array.\n\nParameters\n----------\na : array_like\n    Input array.\n\nReturns\n-------\nshape : tuple of ints\n    The elements of the shape tuple give the lengths of the\n    corresponding array dimensions.\n\nExamples\n--------\n>>> np.shape(np.eye(3))\n(3, 3)\n>>> np.shape([[1, 3]])\n(1, 2)\n>>> np.shape([0])\n(1,)\n>>> np.shape(0)\n()",
  "code": "@array_function_dispatch(_shape_dispatcher)\ndef shape(a):\n    \"\"\"\n    Return the shape of an array.\n    \"\"\"\n    try:\n        result = a.shape\n    except AttributeError:\n        result = asarray(a).shape\n    return result",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.shape(a)"
}
-/

open Std.Do

/-- numpy.shape: Return the shape of an array.

    For a one-dimensional vector, returns its length as a natural number.
    This corresponds to the single element in the shape tuple for 1D arrays
    in NumPy.
    
    In the general NumPy implementation, shape returns a tuple of dimensions.
    For our Vector type, which is inherently one-dimensional, the shape is
    simply the length parameter n.
-/
def shape {α : Type} {n : Nat} (a : Vector α n) : Id Nat :=
  sorry

/-- Specification: numpy.shape returns the length of the vector.

    For a Vector of length n, the shape function returns n.
    This captures the fundamental property that the shape of a 1D array
    is its length.
    
    Precondition: True (shape is defined for all vectors)
    Postcondition: The result equals the length parameter n of the vector
-/
theorem shape_spec {α : Type} {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    shape a
    ⦃⇓result => ⌜result = n⌝⦄ := by
  sorry