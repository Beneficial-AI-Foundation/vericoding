import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.exp: Calculate the exponential of all elements in the input array.

    Computes the exponential function (e^x) element-wise. This is the inverse
    of the natural logarithm function. For each element x in the input array,
    the result contains e^x where e is Euler's number (approximately 2.71828).

    The exponential function has the mathematical property that exp(x + y) = exp(x) * exp(y)
    and exp(0) = 1.

    Returns an array of the same shape as x, containing the exponential values.
-/
def numpy_exp {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map Float.exp)

-- LLM HELPER
lemma float_exp_pos (x : Float) : Float.exp x > 0 := by
  sorry

-- LLM HELPER
lemma float_exp_zero : Float.exp 0 = 1 := by
  sorry

-- LLM HELPER
lemma float_exp_monotone (x y : Float) : x ≤ y → Float.exp x ≤ Float.exp y := by
  sorry

-- LLM HELPER
lemma vector_map_get {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  sorry

/-- Specification: numpy.exp returns a vector where each element is the
    exponential (e^x) of the corresponding element in x.

    Precondition: True (exponential function is defined for all real numbers)
    Postcondition: For all indices i, result[i] = e^(x[i])
    
    Mathematical properties:
    - exp(0) = 1 for any zero elements
    - exp(x) > 0 for all x (exponential is always positive)
    - exp is monotonically increasing
    - exp(x + y) = exp(x) * exp(y) (for addition in the input)
-/
theorem numpy_exp_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_exp x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (x.get i) ∧ 
                   result.get i > 0 ∧
                   (x.get i = 0 → result.get i = 1) ∧
                   (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
  apply Triple.pure_spec
  intro i
  constructor
  · exact vector_map_get x Float.exp i
  constructor
  · rw [vector_map_get]
    exact float_exp_pos (x.get i)
  constructor
  · intro h_zero
    rw [vector_map_get]
    rw [h_zero]
    exact float_exp_zero
  · intro j h_le
    rw [vector_map_get, vector_map_get]
    exact float_exp_monotone (x.get i) (x.get j) h_le