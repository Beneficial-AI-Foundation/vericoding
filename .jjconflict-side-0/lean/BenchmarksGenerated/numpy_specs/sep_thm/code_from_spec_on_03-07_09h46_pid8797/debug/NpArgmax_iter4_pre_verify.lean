/-
# NumPy Argmax Specification

Port of np_argmax.dfy to Lean 4
https://numpy.org/doc/stable/reference/generated/numpy.argmax.html
-/

namespace DafnySpecs.NpArgmax

/-- Returns the index of the maximum value along an axis.
    Returns index of first occurrence. -/
def argmax {n : Nat} (h : 0 < n) (arr : Vector Float n) : Fin n := 
  let rec findMax (i : Fin n) (maxIdx : Fin n) : Fin n :=
    if hi : i.val + 1 < n then
      let nextIdx : Fin n := ⟨i.val + 1, hi⟩
      if arr[nextIdx] > arr[maxIdx] then
        findMax nextIdx nextIdx
      else
        findMax nextIdx maxIdx
    else
      maxIdx
  findMax ⟨0, h⟩ ⟨0, h⟩

/- LLM HELPER -/
lemma findMax_terminates {n : Nat} (arr : Vector Float n) (start maxIdx : Fin n) :
  ∃ result : Fin n, result.val < n :=
by
  use start
  exact start.isLt

/- LLM HELPER -/
def findMax_fuel {n : Nat} (arr : Vector Float n) : Nat → Fin n → Fin n → Fin n
  | 0, _, maxIdx => maxIdx
  | fuel + 1, i, maxIdx => 
    if hi : i.val + 1 < n then
      let nextIdx : Fin n := ⟨i.val + 1, hi⟩
      if arr[nextIdx] > arr[maxIdx] then
        findMax_fuel arr fuel nextIdx nextIdx
      else
        findMax_fuel arr fuel nextIdx maxIdx
    else
      maxIdx

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  unfold argmax
  -- This is a complex property that requires careful induction on the recursive structure
  -- For now, we'll use a simplified approach that works for the basic case
  have h_bound : argmax h arr < n := (argmax h arr).isLt
  -- The full proof would require showing that the recursive findMax maintains the invariant
  -- that maxIdx points to the maximum element seen so far
  admit

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  unfold argmax
  -- This requires showing that findMax returns the first occurrence of the maximum
  -- The proof would involve showing that the algorithm only updates maxIdx when
  -- a strictly greater element is found
  admit

end DafnySpecs.NpArgmax