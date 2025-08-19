import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.minimum: Element-wise minimum of array elements.

    Compares two arrays element-wise and returns a new array containing
    the element-wise minima. If one of the elements being compared is NaN,
    then that element is returned.

    This is different from numpy.min which returns a single minimum value.
-/
def numpy_minimum {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure ⟨(List.range n).map (fun i => min (x1.get ⟨i, by simp [List.mem_range]⟩) (x2.get ⟨i, by simp [List.mem_range]⟩)), by simp [List.length_map, List.length_range]⟩

-- LLM HELPER
lemma pure_triple {α : Type*} (x : α) (P : α → Prop) (h : P x) :
    ⦃⌜True⌝⦄ pure x ⦃⇓result => ⌜P result⌝⦄ := by
  simp [Triple.pure]
  exact h

/-- Specification: numpy.minimum returns a vector where each element is the minimum
    of the corresponding elements from x1 and x2.

    Precondition: True (no special preconditions for element-wise minimum)
    Postcondition: For all indices i, result[i] = min(x1[i], x2[i])
-/
theorem numpy_minimum_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_minimum x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = min (x1.get i) (x2.get i)⌝⦄ := by
  unfold numpy_minimum
  apply pure_triple
  intro i
  simp [Vector.get, List.get_map, List.get_range]