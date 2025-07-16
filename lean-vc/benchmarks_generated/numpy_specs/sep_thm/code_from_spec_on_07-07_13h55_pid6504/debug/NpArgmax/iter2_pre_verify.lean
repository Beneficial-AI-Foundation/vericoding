/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

-- LLM HELPER
def argmax_aux {n : Nat} (arr : Vector Float n) (k : Nat) (best_idx : Nat) : Nat :=
  if k = 0 then best_idx
  else 
    if h : k - 1 < n then
      if h_best : best_idx < n then
        let new_best := if arr[k - 1] > arr[best_idx] then k - 1 else best_idx
        argmax_aux arr (k - 1) new_best
      else best_idx
    else best_idx

-- LLM HELPER  
def find_argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Nat :=
  argmax_aux arr n 0

-- LLM HELPER
lemma find_argmax_lt {n : Nat} (h : 0 < n) (arr : Vector Float n) : find_argmax h arr < n := by
  unfold find_argmax
  have : argmax_aux arr n 0 < n := by
    induction n with
    | zero => contradiction
    | succ n ih => 
      simp [argmax_aux]
      sorry
  exact this

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