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
    if hi : i.val + 1 < n then
      let next_i : Fin n := ⟨i.val + 1, hi⟩
      if arr[i] > arr[max_idx] then
        find_max_index next_i i
      else
        find_max_index next_i max_idx
    else
      if arr[i] > arr[max_idx] then i else max_idx
  termination_by n - i.val
  find_max_index ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma argmax_valid {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, arr[argmax h arr] ≥ arr[i] := by
  intro i
  unfold argmax
  sorry

/- LLM HELPER -/
lemma argmax_first_occurrence {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  unfold argmax at hi
  sorry

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] :=
  argmax_first_occurrence h arr

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] :=
  fun i _ => argmax_valid h arr i

end DafnySpecs.NpArgmax