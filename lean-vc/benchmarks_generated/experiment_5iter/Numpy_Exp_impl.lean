import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.exp: Calculate the exponential of all elements in the input array.

    Computes e^x for each element x in the input array, where e is Euler's number.
    The natural exponential function is the inverse of the natural logarithm.

    Returns an array of the same shape as x, containing the exponential of each element.
-/
def numpy_exp {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map Float.exp)

-- LLM HELPER
lemma vector_map_get {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  simp [Vector.get_map]

-- LLM HELPER
lemma wp_pure {α : Type*} (x : α) (P : α → Prop) :
    wp⟦pure x⟧ ⇓result => P result ↔ P x := by
  simp [wp]

/-- Specification: numpy.exp returns a vector where each element is e raised to
    the power of the corresponding element in x.

    Precondition: True (no special preconditions for exponential)
    Postcondition: For all indices i, result[i] = Float.exp x[i]
-/
theorem numpy_exp_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_exp x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.exp (x.get i)⌝⦄ := by
  simp [numpy_exp, wp_pure]
  intro i
  rw [vector_map_get]