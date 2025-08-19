import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.fromiter",
  "category": "From existing data",
  "description": "Create a new 1-dimensional array from an iterable object",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fromiter.html",
  "doc": "\nCreate a new 1-dimensional array from an iterable object.\n\nParameters\n----------\niter : iterable object\n    An iterable object providing data for the array.\ndtype : data-type\n    The data-type of the returned array.\ncount : int, optional\n    The number of items to read from iterable. The default is -1, which means all data is read.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\nout : ndarray\n    The output array.\n\nExamples\n--------\n>>> iterable = (x*x for x in range(5))\n>>> np.fromiter(iterable, float)\narray([  0.,   1.,   4.,   9.,  16.])\n\nTo read from a text file object:\n\n>>> from io import StringIO\n>>> f = StringIO(\"1 2 3 4\")\n>>> np.fromiter(f.read().split(), dtype=int)\narray([1, 2, 3, 4])\n",
  "code": "@array_function_dispatch(_fromiter_dispatcher)\ndef fromiter(iter, dtype, count=-1, *, like=None):\n    \"\"\"\n    Create a new 1-dimensional array from an iterable object.\n    \"\"\"\n    if like is not None:\n        return _fromiter_with_like(iter, dtype, count=count, like=like)\n\n    return _core_fromiter(iter, dtype, count)",
  "signature": "numpy.fromiter(iter, dtype, count=-1, *, like=None)"
}
-/

/-- Create a new 1-dimensional array from an iterable object.
    Takes the first n elements from the iterable sequence and creates a Vector.
    This models numpy.fromiter with explicit count parameter. -/
def fromiter {α : Type} (n : Nat) (iter : Fin n → α) : Id (Vector α n) :=
  Vector.ofFn iter

/-- Specification: fromiter creates a Vector containing the first n elements 
    from the iterable in order. The resulting Vector has exactly n elements,
    and each element at index i equals the i-th element from the iterable. -/
theorem fromiter_spec {α : Type} (n : Nat) (iter : Fin n → α) :
    ⦃⌜True⌝⦄
    fromiter n iter
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = iter i⌝⦄ := by
  intro h
  simp [fromiter]
  intro i
  rw [Vector.get_ofFn]