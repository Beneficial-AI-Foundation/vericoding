import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.sqrt: Return the non-negative square-root of an array, element-wise.

    Computes the principal square root of each element in the input array.
    For negative input elements, the result is NaN (Not a Number).

    An array of the same shape as x, containing the positive square-root
    of each element in x.
-/
def numpy_sqrt {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  return Vector.ofFn (fun i => Float.sqrt (x.get i))

-- LLM HELPER
lemma float_sqrt_properties (x : Float) : 
  x ≥ 0 → (Float.sqrt x) ^ 2 = x ∧ Float.sqrt x ≥ 0 := by
  intro h
  constructor
  · exact Float.sqrt_sq h
  · exact Float.sqrt_nonneg x

/-- Specification: numpy.sqrt returns a vector where each element is the
    non-negative square root of the corresponding element in x.

    Precondition: True (handles negative values by returning NaN)
    Postcondition: For all indices i, if x[i] ≥ 0 then result[i]² = x[i] and result[i] ≥ 0
-/
theorem numpy_sqrt_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_sqrt x
    ⦃⇓result => ⌜∀ i : Fin n,
      (x.get i ≥ 0 → result.get i ^ 2 = x.get i ∧ result.get i ≥ 0)⌝⦄ := by
  simp [numpy_sqrt]
  intro i h
  simp [Vector.get, Vector.ofFn]
  exact float_sqrt_properties (x.get i) h