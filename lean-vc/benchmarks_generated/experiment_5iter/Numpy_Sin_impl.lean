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
  pure (x.map Float.sin)

-- LLM HELPER
theorem pure_triple_id {α : Type*} {P : α → Prop} (a : α) (h : P a) :
    ⦃⌜True⌝⦄ (pure a : Id α) ⦃⇓result => ⌜P result⌝⦄ := by
  simp [pure, Id.pure]
  exact h

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
  apply pure_triple_id
  intro i
  simp [Vector.get_map]