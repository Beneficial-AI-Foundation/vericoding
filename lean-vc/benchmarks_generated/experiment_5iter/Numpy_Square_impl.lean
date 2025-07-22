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

-- LLM HELPER
lemma vector_get_map {n : Nat} (x : Vector Float n) (f : Float → Float) (i : Fin n) :
    (x.map f).get i = f (x.get i) := by
  rfl

-- LLM HELPER
lemma spec_pure_helper {α : Type} (a : α) : 
    ⦃⌜True⌝⦄ (pure a : Id α) ⦃⇓result => ⌜result = a⌝⦄ := by
  simp [Triple.spec_pure]

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
  apply spec_pure_helper
  intro i
  rw [vector_get_map]