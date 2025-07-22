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
  Id.pure (Vector.zipWith (· + ·) x1 x2)

-- LLM HELPER
lemma vector_zipWith_get {α β γ : Type*} {n : Nat} (f : α → β → γ) (v1 : Vector α n) (v2 : Vector β n) (i : Fin n) :
    (Vector.zipWith f v1 v2).get i = f (v1.get i) (v2.get i) := by
  simp [Vector.zipWith, Vector.get]

/-- Specification: numpy.add returns a vector where each element is the sum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for basic addition)
    Postcondition: For all indices i, result[i] = x1[i] + x2[i]
-/
theorem numpy_add_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_add x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i + x2.get i⌝⦄ := by
  simp [numpy_add, Std.Do.hoareTriple_returnPure, Std.Do.hoareTriple_pure]
  intro i
  exact vector_zipWith_get (· + ·) x1 x2 i