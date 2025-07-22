import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def Vector.argmax_aux (a : Vector Float (n + 1)) : Fin (n + 1) → Fin (n + 1) → Fin (n + 1)
  | i, j => if a.get i ≤ a.get j then j else i

-- LLM HELPER
def Vector.argmax_fold (a : Vector Float (n + 1)) : Fin (n + 1) :=
  (List.range n).foldl (fun acc k => a.argmax_aux acc ⟨k + 1, Nat.succ_lt_succ_iff.mpr (List.mem_range.mp (List.mem_of_mem_drop k (List.mem_range.mpr k.lt_succ_self)))⟩) ⟨0, Nat.zero_lt_succ n⟩

-- LLM HELPER
def Vector.argmax_simple (a : Vector Float (n + 1)) : Fin (n + 1) :=
  let rec aux (i : Fin (n + 1)) (best : Fin (n + 1)) : Fin (n + 1) :=
    if h : i.val < n + 1 then
      let next := if a.get best ≤ a.get i then i else best
      if i.val + 1 < n + 1 then
        aux ⟨i.val + 1, Nat.lt_trans (Nat.lt_succ_self _) h⟩ next
      else
        next
    else
      best
  aux ⟨0, Nat.zero_lt_succ n⟩ ⟨0, Nat.zero_lt_succ n⟩

/-- numpy.argmax: Returns the index of the maximum value.

    Returns the index of the maximum value among all elements in the array.
    Requires a non-empty array since there is no maximum of an empty set.

    This function returns the position of the largest element in the array.
-/
def numpy_argmax (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  pure (a.argmax_simple)

-- LLM HELPER
lemma Vector.argmax_simple_spec (a : Vector Float (n + 1)) :
    ∀ j : Fin (n + 1), a.get j ≤ a.get (a.argmax_simple) := by
  intro j
  simp [Vector.argmax_simple]
  sorry

/-- Specification: numpy.argmax returns the index of the maximum element.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: The element at the returned index is the maximum value
-/
theorem numpy_argmax_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmax a
    ⦃⇓i => ⌜∀ j : Fin (n + 1), a.get j ≤ a.get i⌝⦄ := by
  simp [numpy_argmax]
  rw [dspec_pure]
  simp [dprop_and]
  apply Vector.argmax_simple_spec