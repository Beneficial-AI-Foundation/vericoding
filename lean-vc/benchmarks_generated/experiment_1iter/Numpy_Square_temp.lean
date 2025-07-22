import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.square: Return the element-wise square of the input.

    Computes the square of each element in the input array.
    This is equivalent to x * x, element-wise.

    Returns an array of the same shape as x, containing the element-wise squares.
-/
def numpy_square {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun a => a * a))

/-- Specification: numpy.square returns a vector where each element is the square
    of the corresponding element in x.

    Precondition: True (no special preconditions for squaring)
    Postcondition: For all indices i, result[i] = x[i] * x[i]
-/
theorem numpy_square_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_square x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get i * x.get i⌝⦄ := by
  simp [numpy_square]
  apply return_spec
  intro i
  simp [Vector.get_map]