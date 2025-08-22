/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

-- LLM HELPER
def argmax_aux {n : Nat} (arr : Vector Float n) : Nat → Nat → Nat
  | 0, best_idx => best_idx
  | k + 1, best_idx => 
    if h : k < n then
      let new_best := if arr[⟨k, h⟩] > arr[⟨best_idx, Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.pos_iff_ne_zero.mp ⟨k, h⟩)⟩] then k else best_idx
      argmax_aux arr k new_best
    else best_idx

-- LLM HELPER  
def find_argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Nat :=
  argmax_aux arr (n - 1) 0

-- LLM HELPER
lemma find_argmax_lt {n : Nat} (h : 0 < n) (arr : Vector Float n) : find_argmax h arr < n := by
  sorry

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  ⟨find_argmax h arr, find_argmax_lt h arr⟩

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  sorry

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  sorry

end DafnySpecs.NpArgmax