import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "NDArray",
  "category": "Core Type Aliases",
  "description": "Generic type alias for numpy.ndarray that is generic with respect to its dtype",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.NDArray",
  "doc": "A generic type alias for numpy.ndarray[Any, dtype[+ScalarT]].\n\nCan be used during runtime for typing arrays with a given dtype and unspecified shape.\n\nExamples:\n>>> import numpy as np\n>>> import numpy.typing as npt\n\n>>> print(npt.NDArray)\nnumpy.ndarray[typing.Any, numpy.dtype[+_ScalarType_co]]\n\n>>> print(npt.NDArray[np.float64])\nnumpy.ndarray[typing.Any, numpy.dtype[numpy.float64]]\n\n>>> NDArrayInt = npt.NDArray[np.int_]\n>>> a: NDArrayInt = np.arange(10)",
  "code": "# From numpy._typing._array_like.py\nfrom ._shape import _AnyShape\n\n_ScalarT = TypeVar(\"_ScalarT\", bound=np.generic)\n\nNDArray: TypeAlias = np.ndarray[_AnyShape, dtype[_ScalarT]]"
}
-/

open Std.Do

/-- NDArray represents a generic n-dimensional array with elements of type T.
    This is a Vector-based implementation that provides type safety for array dimensions.
    The type parameter T represents the dtype (element type) of the array. -/
def NDArray (T : Type) {n : Nat} : Type := Vector T n

/-- Create an NDArray from a Vector. This constructor provides a type-safe way 
    to create NDArray instances from Vector data. -/
def fromVector {T : Type} {n : Nat} (v : Vector T n) : Id (NDArray T (n := n)) :=
  sorry

/-- Specification: fromVector creates an NDArray that preserves all properties
    of the input Vector. This captures the fundamental property that NDArray is a 
    type-safe wrapper around Vector that maintains element access, size guarantees,
    and type constraints. The specification ensures that the resulting NDArray
    contains exactly the same elements as the input Vector in the same order. -/
theorem fromVector_spec {T : Type} {n : Nat} (v : Vector T n) :
    ⦃⌜True⌝⦄
    fromVector v
    ⦃⇓result => ⌜result.size = n ∧ 
                 (∀ i : Fin n, result.get i = v.get i) ∧
                 (∀ i j : Fin n, i = j → result.get i = result.get j)⌝⦄ := by
  sorry