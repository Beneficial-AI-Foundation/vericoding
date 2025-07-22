import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.cos: Trigonometric cosine, element-wise.

    The cosine is one of the fundamental functions of trigonometry.
    For a real number x interpreted as an angle in radians, cos(x)
    gives the x-coordinate of the point on the unit circle.

    Returns an array of the same shape as x, containing the cosine of each element.
-/
def numpy_cos {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map Float.cos)

/-- Specification: numpy.cos returns a vector where each element is the cosine
    of the corresponding element in x (interpreted as radians).

    Precondition: True (no special preconditions for cosine)
    Postcondition: For all indices i, result[i] = Float.cos x[i]
-/
theorem numpy_cos_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_cos x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.cos (x.get i)⌝⦄ := by
  unfold numpy_cos
  simp [swp_pure]
  intro i
  simp [Vector.get_map]