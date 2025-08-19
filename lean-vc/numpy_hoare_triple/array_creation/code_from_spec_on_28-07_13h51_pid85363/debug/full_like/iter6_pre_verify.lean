import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.full_like: Return a full array with the same shape and type as a given array.

    Creates a new array with the same shape as the input array `a`, where all
    elements are set to the specified `fill_value`. This is useful for creating
    arrays of a specific constant value while preserving the shape of an existing
    array.

    The actual type of fill_value will be cast to match the array's type,
    similar to numpy's behavior where 0.1 becomes 0 for integer arrays.
-/
def numpy_full_like {n : Nat} (a : Vector Float n) (fill_value : Float) : Id (Vector Float n) :=
  pure ⟨Array.mkArray n fill_value, by simp [Array.size_mkArray]⟩

-- LLM HELPER
lemma array_get_mkArray {α : Type} (n : Nat) (x : α) (i : Fin n) :
    (Array.mkArray n x)[i]'(by simp [Array.size_mkArray]; exact i.isLt) = x := by
  simp [Array.getElem_mkArray]

/-- Specification: numpy.full_like returns a vector with the same shape as `a`
    where every element equals `fill_value`.

    Precondition: True (no special preconditions needed)
    Postcondition: The result has the same length as `a` and all elements equal `fill_value`
-/
theorem numpy_full_like_spec {n : Nat} (a : Vector Float n) (fill_value : Float) :
    ⦃⌜True⌝⦄
    numpy_full_like a fill_value
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = fill_value⌝⦄ := by
  simp [numpy_full_like, Triple.pre_post]
  intro i
  simp [Vector.get]
  apply array_get_mkArray