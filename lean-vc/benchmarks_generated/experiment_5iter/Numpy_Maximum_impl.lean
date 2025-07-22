import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.maximum: Element-wise maximum of array elements.

    Compares two arrays element-wise and returns a new array containing
    the element-wise maxima. If one of the elements being compared is NaN,
    then that element is returned.

    This is different from numpy.max which returns a single maximum value.
-/
def numpy_maximum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn fun i => max (x1.get i) (x2.get i))

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} (f : Fin n → Float) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

/-- Specification: numpy.maximum returns a vector where each element is the maximum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for element-wise maximum)
    Postcondition: For all indices i, result[i] = max(x1[i], x2[i])
-/
theorem numpy_maximum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_maximum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = max (x1.get i) (x2.get i)⌝⦄ := by
  simp [numpy_maximum, pure]
  intro i
  rw [vector_get_ofFn]