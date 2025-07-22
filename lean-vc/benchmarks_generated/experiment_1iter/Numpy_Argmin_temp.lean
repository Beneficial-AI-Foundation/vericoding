import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def find_min_index_aux (a : Vector Float (n + 1)) (current_min_idx : Fin (n + 1)) (j : Fin (n + 1)) : Fin (n + 1) :=
  if a.get j < a.get current_min_idx then j else current_min_idx

-- LLM HELPER
def find_min_index (a : Vector Float (n + 1)) : Fin (n + 1) :=
  let rec aux (current_min_idx : Fin (n + 1)) (remaining : List (Fin (n + 1))) : Fin (n + 1) :=
    match remaining with
    | [] => current_min_idx
    | j :: rest => 
      let new_min_idx := if a.get j < a.get current_min_idx then j else current_min_idx
      aux new_min_idx rest
  aux 0 (List.range (n + 1)).attach.map (fun ⟨i, hi⟩ => ⟨i, Nat.lt_succ_of_lt (List.mem_range.mp hi)⟩)

-- LLM HELPER
def simple_argmin (a : Vector Float (n + 1)) : Fin (n + 1) :=
  Id.run do
    let mut min_idx : Fin (n + 1) := 0
    for i in List.range (n + 1) do
      if h : i < n + 1 then
        let idx : Fin (n + 1) := ⟨i, h⟩
        if a.get idx < a.get min_idx then
          min_idx := idx
    return min_idx

/-- numpy.argmin: Returns the index of the minimum value.

    Returns the index of the minimum value among all elements in the array.
    Requires a non-empty array since there is no minimum of an empty set.

    This function returns the position of the smallest element in the array.
-/
def numpy_argmin (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  Id.pure (simple_argmin a)

-- LLM HELPER
lemma simple_argmin_is_minimum (a : Vector Float (n + 1)) :
    ∀ j : Fin (n + 1), a.get (simple_argmin a) ≤ a.get j := by
  sorry

/-- Specification: numpy.argmin returns the index of the minimum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the minimum value
-/
theorem numpy_argmin_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmin a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get i ≤ a.get j⌝⦄ := by
  simp [numpy_argmin]
  apply triple_pure
  simp
  exact simple_argmin_is_minimum a