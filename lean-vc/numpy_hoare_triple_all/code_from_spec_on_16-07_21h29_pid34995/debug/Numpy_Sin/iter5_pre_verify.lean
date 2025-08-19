import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.sin: Trigonometric sine, element-wise.

    The sine is one of the fundamental functions of trigonometry.
    For a real number x interpreted as an angle in radians, sin(x)
    gives the y-coordinate of the point on the unit circle.

    Returns an array of the same shape as x, containing the sine of each element.
-/
def numpy_sin {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  x.map Float.sin

-- LLM HELPER
lemma vector_map_get {α β : Type*} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  rfl

/-- Specification: numpy.sin returns a vector where each element is the sine
    of the corresponding element in x (interpreted as radians).

    Precondition: True (no special preconditions for sine)
    Postcondition: For all indices i, result[i] = Float.sin x[i]
-/
theorem numpy_sin_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_sin x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.sin (x.get i)⌝⦄ := by
  rw [numpy_sin]
  apply Triple.return_spec
  intro i
  exact vector_map_get x Float.sin i