import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.concatenate: Join a sequence of arrays along an existing axis.

    For 1D arrays, concatenate joins arrays end-to-end. This is the
    simplest form of concatenation - appending one array after another.
    The result has length equal to the sum of input lengths.

    This version handles concatenating two 1D arrays. The general version
    would handle a list of arrays.
-/
def numpy_concatenate {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    Id (Vector Float (n + m)) :=
  Id.pure ⟨a.val ++ b.val, by simp [Vector.length_val]⟩

/-- Specification: numpy.concatenate appends the second array after the first.

    Precondition: True (no special preconditions for basic concatenation)
    Postcondition: First n elements come from a, next m elements come from b
-/
theorem numpy_concatenate_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_concatenate a b
    ⦃⇓result => ⌜(∀ i : Fin n, result.get (i.castAdd m) = a.get i) ∧
                (∀ j : Fin m, result.get (j.natAdd n) = b.get j)⌝⦄ := by
  simp [numpy_concatenate, Id.pure]
  constructor
  · intro i
    simp [Vector.get_mk, List.getElem_append_left]
  · intro j
    simp [Vector.get_mk, List.getElem_append_right]
    rw [Vector.length_val]