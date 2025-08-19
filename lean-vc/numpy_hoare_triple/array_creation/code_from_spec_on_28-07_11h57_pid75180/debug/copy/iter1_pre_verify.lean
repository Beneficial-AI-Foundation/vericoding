import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.copy",
  "category": "From existing data",
  "description": "Return an array copy of the given object",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.copy.html",
  "doc": "\nReturn an array copy of the given object.\n\nParameters\n----------\na : array_like\n    Input data.\norder : {'C', 'F', 'A', 'K'}, optional\n    Controls the memory layout of the copy. 'C' means C-order, 'F' means Fortran-order, \n    'A' means 'F' if a is Fortran contiguous, 'C' otherwise. 'K' means match the layout \n    of a as closely as possible.\nsubok : bool, optional\n    If True, then sub-classes will be passed-through, otherwise the returned array will \n    be forced to be a base-class array (defaults to False).\n\nReturns\n-------\narr : ndarray\n    Array interpretation of a.\n\nExamples\n--------\nCreate an array x, with a reference y and a copy z:\n\n>>> x = np.array([1, 2, 3])\n>>> y = x\n>>> z = np.copy(x)\n\nNote that, when we modify x, y changes, but not z:\n\n>>> x[0] = 10\n>>> x[0] == y[0]\nTrue\n>>> x[0] == z[0]\nFalse\n\nNote that np.copy clears previously set WRITEABLE=False flag.\n",
  "code": "@array_function_dispatch(_copy_dispatcher)\ndef copy(a, order='K', subok=False):\n    \"\"\"\n    Return an array copy of the given object.\n    \"\"\"\n    return array(a, order=order, subok=subok, copy=True)",
  "signature": "numpy.copy(a, order='K', subok=False)"
}
-/

/-- Return an array copy of the given object. 
    The copy has the same shape and values as the original array, 
    but occupies different memory locations. -/
def copy {n : Nat} (a : Vector α n) : Id (Vector α n) :=
  pure ⟨a.data, a.isValid⟩

/-- Specification: copy returns a vector with identical values but independent memory.
    The resulting vector has the same size and all elements equal to the original,
    ensuring that the copy is element-wise equivalent to the original. -/
theorem copy_spec {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    copy a
    ⦃⇓result => ⌜∀ i : Fin n, result[i] = a[i]⌝⦄ := by
  simp [copy]
  apply has_post_of_post
  simp
  intro i
  rfl