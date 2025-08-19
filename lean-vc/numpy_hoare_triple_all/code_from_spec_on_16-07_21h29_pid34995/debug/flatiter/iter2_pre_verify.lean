import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.flatiter",
  "category": "Iterating over arrays",
  "description": "Flat iterator object to iterate over arrays",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.flatiter.html",
  "doc": "Flat iterator object to iterate over arrays.\n\nA \`flatiter\` iterator is returned by \`\`x.flat\`\` for any array \`x\`. It allows iterating over the array as if it were a 1-D array, either in a for-loop or by calling its \`next\` method.\n\nIteration is done in row-major, C-style order (the last index varying the fastest). The iterator can also be indexed using basic slicing or advanced indexing.\n\nNotes\n-----\nA \`flatiter\` iterator can not be constructed directly from Python code by calling the \`flatiter\` constructor.",
  "code": "# C implementation - flatiter is implemented in C"
}
-/

/-- numpy.flatiter: Flat iterator object to iterate over arrays.
    
    A flatiter iterator provides a flattened view of an array for iteration purposes.
    It allows accessing elements of a multi-dimensional array as if it were 1-dimensional,
    following row-major (C-style) order where the last index varies fastest.
    
    The iterator supports indexing and provides sequential access to all elements
    in the array following the memory layout order.
-/
def numpy_flatiter {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  pure a

/-- Specification: numpy.flatiter creates a flat iterator over the array.
    
    Precondition: True (no special preconditions for creating a flat iterator)
    Postcondition: The result preserves all elements in row-major order,
                   providing sequential access to the flattened array elements
-/
theorem numpy_flatiter_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_flatiter a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get i⌝⦄ := by
  simp [numpy_flatiter]
  intro i
  rfl