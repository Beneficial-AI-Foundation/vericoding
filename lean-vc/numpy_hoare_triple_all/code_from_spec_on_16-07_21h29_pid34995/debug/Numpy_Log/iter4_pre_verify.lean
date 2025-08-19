import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.log: Natural logarithm, element-wise.

    The natural logarithm log is the inverse of the exponential function,
    so that log(exp(x)) = x. The natural logarithm is logarithm base e.

    Returns an array of the same shape as x, containing the natural logarithm
    of each element in x.
-/
def numpy_log {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map Float.log)

-- LLM HELPER
lemma vector_get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  simp [Vector.get, Vector.map]

/-- Specification: numpy.log returns a vector where each element is the natural
    logarithm of the corresponding element in x.

    Precondition: All elements must be positive (x[i] > 0)
    Postcondition: For all indices i, result[i] = Float.log x[i]
-/
theorem numpy_log_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜∀ i : Fin n, x.get i > 0⌝⦄
    numpy_log x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.log (x.get i)⌝⦄ := by
  simp [numpy_log]
  intro i
  rw [vector_get_map]