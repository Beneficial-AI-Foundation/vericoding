import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.where: Return elements chosen from x or y depending on condition.

    For each element, returns x[i] if condition[i] is true, else y[i].
    All three arrays must have the same shape.

    This function enables conditional selection between two arrays.
-/
def numpy_where (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) : Id (Vector Float n) :=
  Vector.ofFn fun i => if condition.get i then x.get i else y.get i

-- LLM HELPER
lemma Vector.get_ofFn {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

/-- Specification: numpy.where performs element-wise conditional selection.

    Precondition: True (same-size constraint is in the type)
    Postcondition: Each element is selected from x or y based on condition
-/
theorem numpy_where_spec (condition : Vector Bool n) (x : Vector Float n) (y : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_where condition x y
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = if condition.get i then x.get i else y.get i⌝⦄ := by
  simp [numpy_where]
  apply Triple.pure
  intro _
  simp [Vector.get_ofFn]