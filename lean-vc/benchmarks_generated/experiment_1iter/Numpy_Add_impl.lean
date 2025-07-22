import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.add: Add arguments element-wise.

    Adds two vectors element-wise. If the vectors have the same shape,
    each element of the result is the sum of the corresponding elements
    from the input vectors.

    This is equivalent to x1 + x2 in terms of array broadcasting.
-/
def numpy_add {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => x1.get i + x2.get i)

/-- Specification: numpy.add returns a vector where each element is the sum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic addition)
    Postcondition: For all indices i, result[i] = x1[i] + x2[i]
-/
theorem numpy_add_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_add x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i + x2.get i⌝⦄ := by
  simp [numpy_add]
  simp [Vector.get_ofFn]