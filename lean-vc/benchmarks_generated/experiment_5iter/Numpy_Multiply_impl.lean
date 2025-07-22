import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.multiply: Multiply arguments element-wise.

    Multiplies arguments element-wise. If the arrays have the same shape,
    each element of the result is the product of the corresponding elements
    from the input arrays.

    This is equivalent to x1 * x2 in terms of array broadcasting.
-/
def numpy_multiply {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  Vector.zipWith (· * ·) x1 x2

-- LLM HELPER
lemma vector_zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (v1 : Vector α n) (v2 : Vector β n) (i : Fin n) :
  (Vector.zipWith f v1 v2).get i = f (v1.get i) (v2.get i) := by
  rfl

/-- Specification: numpy.multiply returns a vector where each element is the product
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic multiplication)
    Postcondition: For all indices i, result[i] = x1[i] * x2[i]
-/
theorem numpy_multiply_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_multiply x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i * x2.get i⌝⦄ := by
  simp [numpy_multiply]
  apply Triple.pure_spec
  intro i
  exact vector_zipWith_get (· * ·) x1 x2 i