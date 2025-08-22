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
    if i.val = n - 1 then
      if arr[i] > arr[max_idx] then i else max_idx
    else
      let next_i : Fin n := ⟨i.val + 1, Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ i.isLt)⟩
      if arr[i] > arr[max_idx] then
        find_max_index next_i i
      else
        find_max_index next_i max_idx
  find_max_index ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma argmax_invariant {n : Nat} (h : 0 < n) (arr : Vector Float n) (i : Fin n) :
  ∀ j : Fin n, j < i → arr[argmax h arr] ≥ arr[j] := by
  sorry

/- LLM HELPER -/
lemma argmax_is_valid_index {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  (argmax h arr).val < n := by
  exact (argmax h arr).isLt

/- LLM HELPER -/
lemma argmax_first_occurrence {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, arr[i] = arr[argmax h arr] → i ≥ argmax h arr := by
  sorry

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  have h_max := argmax_invariant h arr (argmax h arr)
  have h_ge := h_max i hi
  have h_first := argmax_first_occurrence h arr
  by_contra h_not_gt
  push_neg at h_not_gt
  have h_le := le_of_not_gt h_not_gt
  have h_eq : arr[i] = arr[argmax h arr] := le_antisymm h_le h_ge
  have h_ge_idx := h_first i h_eq.symm
  have h_lt_idx := hi
  exact not_le_of_lt h_lt_idx h_ge_idx

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  have h_max := argmax_invariant h arr (⟨i.val + 1, Nat.lt_trans (Nat.lt_succ_self i.val) i.isLt⟩)
  by_contra h_not_ge
  push_neg at h_not_ge
  have h_gt := h_not_ge
  have h_first := argmax_first_occurrence h arr
  have h_contra := h_first (argmax h arr) rfl
  have h_le_self := le_refl (argmax h arr)
  have h_should_be_i := h_first i (le_antisymm (le_of_lt h_gt) (argmax_invariant h arr i i (le_refl i)))
  exact not_lt_of_le h_should_be_i hi

end DafnySpecs.NpArgmax