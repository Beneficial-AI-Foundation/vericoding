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
    if i.val + 1 < n then
      let nextIdx : Fin n := ⟨i.val + 1, Nat.lt_of_succ_lt (Nat.lt_succ_of_lt i.isLt)⟩
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

/-- Specification: All elements before the maximum index are strictly less than the maximum -/
theorem argmax_is_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, i < argmax h arr → arr[argmax h arr] > arr[i] := by
  intro i hi
  simp [argmax]
  by_cases h1 : i.val = 0
  · simp [h1]
    cases' n with n'
    · contradiction
    · simp
      rfl
  · simp at h1
    have : i.val > 0 := Nat.pos_of_ne_zero h1
    rfl

/-- Specification: All elements after the maximum index are less than or equal to the maximum -/
theorem argmax_is_first_max {n : Nat} (h : 0 < n) (arr : Vector Float n) :
  ∀ i : Fin n, argmax h arr < i → arr[argmax h arr] ≥ arr[i] := by
  intro i hi
  simp [argmax]
  by_cases h1 : i.val = 0
  · simp [h1] at hi
    exact False.elim (Nat.not_lt_zero _ hi.val)
  · simp at h1
    have : i.val > 0 := Nat.pos_of_ne_zero h1
    rfl

end DafnySpecs.NpArgmax