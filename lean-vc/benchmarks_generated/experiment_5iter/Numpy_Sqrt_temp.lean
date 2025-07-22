import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def float_nan : Float := 0.0 / 0.0

/-- numpy.sqrt: Return the non-negative square-root of an array, element-wise.

    Computes the principal square root of each element in the input array.
    For negative input elements, the result is NaN (Not a Number).

    An array of the same shape as x, containing the positive square-root
    of each element in x.
-/
def numpy_sqrt {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun f => if f ≥ 0 then Float.sqrt f else float_nan))

-- LLM HELPER
lemma float_sqrt_spec (f : Float) (h : f ≥ 0) : Float.sqrt f ^ 2 = f ∧ Float.sqrt f ≥ 0 := by
  constructor
  · exact Float.sqrt_sq h
  · exact Float.sqrt_nonneg f

-- LLM HELPER
lemma vector_map_get {α β : Type} {n : Nat} (v : Vector α n) (f : α → β) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  simp [Vector.get_map]

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
  rw [vector_map_get]
  simp [h]
  exact float_sqrt_spec (x.get i) h