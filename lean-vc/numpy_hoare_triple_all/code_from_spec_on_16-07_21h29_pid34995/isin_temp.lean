import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.isin: Element-wise test for membership in another array.

    Calculates `element in test_elements`, broadcasting over `element` only.
    Returns a boolean array of the same shape as `element` that is True
    where an element of `element` is in `test_elements` and False otherwise.

    This is an element-wise function version of the python keyword `in`.
    For 1-D arrays, this is roughly equivalent to:
    `np.array([item in test_elements for item in element])`
-/
def numpy_isin {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) : Id (Vector Bool n) := do
  let result_list := List.range n |>.map (fun i => 
    let elem := element.get ⟨i, by simp [List.length_range]; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.le_refl _)))⟩
    List.range m |>.any (fun j => elem == test_elements.get ⟨j, by simp [List.length_range]; exact Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le (Nat.le_refl _)))⟩)))
  have h : result_list.length = n := by
    simp [List.length_map, List.length_range]
  return Vector.mk result_list

-- LLM HELPER
lemma list_range_length (n : Nat) : (List.range n).length = n := by
  simp [List.length_range]

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  simp [List.length_map]

-- LLM HELPER
lemma vector_get_mk {α : Type*} (l : List α) (h : l.length = n) (i : Fin n) : 
    (Vector.mk l).get i = l.get ⟨i.val, by rw [← h]; exact i.isLt⟩ := by
  simp [Vector.get]

-- LLM HELPER  
lemma list_any_iff {α : Type*} (p : α → Bool) (l : List α) : 
    l.any p = true ↔ ∃ x ∈ l, p x = true := by
  simp [List.any_eq_true]

-- LLM HELPER
lemma list_mem_range_iff (i j : Nat) : i ∈ List.range j ↔ i < j := by
  simp [List.mem_range]

-- LLM HELPER
lemma beq_eq_true_iff {α : Type*} [BEq α] (a b : α) : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    exact eq_of_beq h
  · intro h
    rw [h]
    exact beq_self_eq_true

/-- Specification: numpy.isin returns a boolean vector where each element indicates
    whether the corresponding element in the input vector is found in test_elements.

    Precondition: True (no special preconditions needed)
    Postcondition: For all indices i, result[i] = true iff element[i] is in test_elements
-/
theorem numpy_isin_spec {n m : Nat} (element : Vector Float n) (test_elements : Vector Float m) :
    ⦃⌜True⌝⦄
    numpy_isin element test_elements
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = true ↔ ∃ j : Fin m, element.get i = test_elements.get j⌝⦄ := by
  simp [numpy_isin, Std.Do.pure_spec]
  constructor
  · trivial
  · intro i
    simp [Vector.get, Vector.mk]
    rw [List.get_map]
    simp [list_any_iff]
    constructor
    · intro h
      obtain ⟨x, hx_mem, hx_eq⟩ := h
      rw [list_mem_range_iff] at hx_mem
      use ⟨x, hx_mem⟩
      rw [beq_eq_true_iff] at hx_eq
      exact hx_eq
    · intro h
      obtain ⟨j, hj_eq⟩ := h
      use j.val
      constructor
      · rw [list_mem_range_iff]
        exact j.isLt
      · rw [beq_eq_true_iff]
        exact hj_eq