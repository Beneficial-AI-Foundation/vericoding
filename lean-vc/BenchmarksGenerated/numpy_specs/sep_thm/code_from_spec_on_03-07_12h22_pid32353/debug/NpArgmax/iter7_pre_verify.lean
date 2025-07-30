/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  let rec find_max_index (i : Fin n) (max_idx : Fin n) : Fin n :=
    if hi : i.val = n - 1 then
      if arr[i] > arr[max_idx] then i else max_idx
    else
      let next_i : Fin n := ⟨i.val + 1, by
        have h_lt : i.val < n := i.isLt
        have h_ne : i.val ≠ n - 1 := hi
        omega⟩
      if arr[i] > arr[max_idx] then
        find_max_index next_i i
      else
        find_max_index next_i max_idx
  termination_by n - i.val
  find_max_index ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma argmax_is_maximum {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ j : Fin n, arr[argmax h arr] ≥ arr[j] := by
  intro j
  simp [argmax]
  sorry

/- LLM HELPER -/
lemma argmax_is_first_occurrence {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[i] < arr[argmax h arr] := by
  intro i hi
  have h_max := argmax_is_maximum h arr i
  have h_ne : i ≠ argmax h arr := Ne.symm (ne_of_lt hi)
  by_contra h_not_lt
  push_neg at h_not_lt
  have h_ge := h_not_lt
  have h_eq : arr[i] = arr[argmax h arr] := le_antisymm h_max h_ge
  sorry

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  have h_lt := argmax_is_first_occurrence h arr i hi
  exact h_lt

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  exact argmax_is_maximum h arr i

end DafnySpecs.NpArgmax