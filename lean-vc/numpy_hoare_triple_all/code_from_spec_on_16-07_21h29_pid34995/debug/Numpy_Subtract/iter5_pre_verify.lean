import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.subtract: Subtract arguments, element-wise.

    Subtracts arguments element-wise. If the arrays have the same shape,
    each element of the result is the difference of the corresponding elements
    from the input arrays.

    This is equivalent to x1 - x2 in terms of array broadcasting.
-/
def numpy_subtract {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.zipWith (· - ·) x1 x2)

-- LLM HELPER
lemma Vector.get_zipWith_lemma {α β γ : Type*} {n : Nat} (f : α → β → γ) (v1 : Vector α n) (v2 : Vector β n) (i : Fin n) :
    (Vector.zipWith f v1 v2).get i = f (v1.get i) (v2.get i) := by
  simp [Vector.zipWith, Vector.get]

/-- Specification: numpy.subtract returns a vector where each element is the difference
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic subtraction)
    Postcondition: For all indices i, result[i] = x1[i] - x2[i]
-/
theorem numpy_subtract_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_subtract x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i - x2.get i⌝⦄ := by
  simp [numpy_subtract]
  apply Triple.pure
  simp
  intro i
  rw [Vector.get_zipWith_lemma]